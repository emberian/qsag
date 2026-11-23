module
/-
# Qsag.Spec.IdealAggregate — Ideal Succinct Signature Aggregation Specification

Layer-0 ideal specification for succinct post-quantum signature aggregation and binary merge trees:
1. Public `AggregateStatement` binding roster public keys, signer bitmap `B`, and message digest,
2. Exact witness validity (`ValidAggregateWitness`: every set bit `i` in `B` carries a valid
   individual signature `verify (pks i) msg (sigs i) = true`),
3. Inductive binary `AggregateMergeTree` verifying hierarchical shard-proof composition with
   disjoint signer bitmaps (`b₁ &&& b₂ = 0`), and
4. Knowledge-extraction soundness contract `AggregateExtractorSound ℰ … oracle q ε`, a
   proposition about the verifier and the extractor: the extractor belongs to the class `ℰ`, and
   against every prover that reads only its own coins and the answers of the sampled hash
   oracle, the probability that the verifier accepts while the extractor's witness map (a
   function of the oracle transcript, the statement and the proof) is not valid and the
   transcript contains no collision of the oracle is at most `ε`. The class matters: an
   unrestricted extractor may search the signature space, and then the accept-all verifier
   satisfies the contract with `ε = 0` when every statement is satisfiable
   (`acceptAll_alwaysValid_unrestricted_extractorSound`). `StraightLineExtractor` is the class
   of extractors that return only signatures carried by the proof or decoded from the
   transcript; for it accept-all is refuted without any unsatisfiability hypothesis
   (`acceptAll_not_straightLine_extractorSound`).
5. Corruption scope: the prover is adversarial; validators are not parties and no key material
   is held (see the section on knowledge soundness).
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-- Public statement verified by a succinct aggregate signature proof over a `numValidators`-validator roster. -/
structure AggregateStatement (PK : Type) (numValidators : Nat) where
  roster : Fin numValidators → PK
  bitmap : BitVec numValidators
  message : Bytes

/-- Witness for `AggregateStatement`: a partial map supplying an individual signature for every
    active validator index `i` where `bitmap.getLsbD i.val = true`. -/
def ValidAggregateWitness {PK Sig : Type} {numValidators : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (stmt : AggregateStatement PK numValidators)
    (sigs : Fin numValidators → Option Sig) : Prop :=
  ∀ i : Fin numValidators,
    stmt.bitmap.getLsbD i.val = true →
    match sigs i with
    | none => False
    | some sig => verifySingle (stmt.roster i) stmt.message sig = true

theorem ValidAggregateWitness_iff {PK Sig : Type} {numValidators : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (stmt : AggregateStatement PK numValidators)
    (sigs : Fin numValidators → Option Sig) :
    ValidAggregateWitness verifySingle stmt sigs ↔
      ∀ i : Fin numValidators,
        stmt.bitmap.getLsbD i.val = true →
        ∃ sig : Sig, sigs i = some sig ∧ verifySingle (stmt.roster i) stmt.message sig = true := by
  unfold ValidAggregateWitness
  constructor
  · intro h i hAct
    have hi := h i hAct
    cases hs : sigs i with
    | none => rw [hs] at hi; exact False.elim hi
    | some sig => rw [hs] at hi; exact ⟨sig, rfl, hi⟩
  · intro h i hAct
    obtain ⟨sig, hs, hv⟩ := h i hAct
    rw [hs]
    exact hv

theorem ValidAggregateWitness.intro {PK Sig : Type} {numValidators : Nat}
    {verifySingle : PK → Bytes → Sig → Bool}
    {stmt : AggregateStatement PK numValidators}
    {sigs : Fin numValidators → Option Sig}
    (h : ∀ i : Fin numValidators,
      stmt.bitmap.getLsbD i.val = true →
      ∃ sig : Sig, sigs i = some sig ∧ verifySingle (stmt.roster i) stmt.message sig = true) :
    ValidAggregateWitness verifySingle stmt sigs :=
  (ValidAggregateWitness_iff verifySingle stmt sigs).mpr h

/-- Binary merge tree over bitmaps of width `w`, ensuring child shards cover disjoint validator subsets. -/
inductive BitmapMergeTree (w : Nat) where
  | leaf (bm : BitVec w) : BitmapMergeTree w
  | merge (left right : BitmapMergeTree w) : BitmapMergeTree w
  deriving DecidableEq, Repr

/-- Combined signer bitmap at the root of a `BitmapMergeTree`. -/
def BitmapMergeTree.rootBitmap {w : Nat} : BitmapMergeTree w → BitVec w
  | .leaf bm => bm
  | .merge l r => l.rootBitmap ||| r.rootBitmap

/-- Structural well-formedness: every internal `.merge` node combines strictly disjoint bitmaps. -/
def BitmapMergeTree.DisjointMerges {w : Nat} : BitmapMergeTree w → Bool
  | .leaf _ => true
  | .merge l r =>
    l.DisjointMerges && r.DisjointMerges && decide (l.rootBitmap &&& r.rootBitmap = 0#w)

/-- Constructively combine two disjoint witness maps along a valid `BitmapMergeTree.merge`. -/
def mergeWitnessMaps {Sig : Type} {w : Nat}
    (bmL : BitVec w)
    (wL wR : Fin w → Option Sig) : Fin w → Option Sig :=
  fun i => if bmL.getLsbD i.val then wL i else wR i

/-- Merging two valid aggregate witnesses over disjoint bitmaps produces a valid witness for
    the bitwise-OR bitmap `bmL ||| bmR`! -/
theorem mergeWitnessMaps_valid {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (roster : Fin w → PK) (msg : Bytes)
    (bmL bmR : BitVec w)
    (wL wR : Fin w → Option Sig)
    (hL : ValidAggregateWitness verifySingle ⟨roster, bmL, msg⟩ wL)
    (hR : ValidAggregateWitness verifySingle ⟨roster, bmR, msg⟩ wR) :
    ValidAggregateWitness verifySingle ⟨roster, bmL ||| bmR, msg⟩
      (mergeWitnessMaps bmL wL wR) := by
  intro i hOr
  rw [BitVec.getLsbD_or] at hOr
  unfold mergeWitnessMaps
  cases hbL : bmL.getLsbD i.val
  · rw [hbL, Bool.false_or] at hOr
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hR i hOr
  · simp only [↓reduceIte]
    exact hL i hbL

/-! ## Knowledge soundness in the oracle model

The experiment has two parties. The challenger samples the hash oracle `oracle c` from its
coin `c`. The prover is an oracle program: it reads its own coin and the oracle's answers, and
outputs a statement and a proof. The challenger records the prover's queries; at most `q` are
answered. The extractor is a function of that transcript, the statement and the proof, and of
nothing else. The prover loses on a coin when the verifier rejects, when the extracted witness
map is valid, or when two different recorded queries have the same answer.

`AggregateExtractorSound ℰ … q ε` states that the extractor belongs to the class `ℰ` and that
every prover wins with probability at most `ε`. The bound `ε` is an index of the proposition,
not a field: with `ε = 1` it holds for every verifier (`aggregateExtractorSound_one`), and for
the verifier that accepts everything and a straight-line extractor it holds for no `ε < 1`
(`acceptAll_not_straightLine_extractorSound`).

What stays information-theoretic: provers are arbitrary oracle programs, with a query budget
and no running-time bound; the decoder of a straight-line extractor is an arbitrary function of
one byte string; the oracle family carries no uniformity law. Nothing here transfers to
unforgeability of the aggregate against a bounded adversary.

**Corruption scope.** The aggregator / prover is adversarial: the proposition quantifies over
all of them. Validators are not parties of this functionality and it holds no key material. A
valid witness is one verifying signature per active signer, whoever produced it, so a validator
whose key is compromised counts as a signer. That an honest validator's signature was produced
by that validator is unforgeability of `verifySingle`, which is a separate hypothesis; the
second branch of `AggregateSoundnessOutcome.signer_trichotomy` (the run's extractor output is a
verifying signature of a validator that did not participate) is where it enters. -/

private theorem aggItePos {α : Type} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem aggIteNeg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem aggAndSplit {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

/-- Break data: a candidate collision of the commitment hash. -/
structure AggregateBreak where
  m₁ : Bytes
  m₂ : Bytes
  deriving DecidableEq, Repr

/-- `b` is a collision of the commitment hash `H`: two different inputs with the same digest. -/
def ValidBreak (H : Bytes → Bytes) (b : AggregateBreak) : Prop :=
  b.m₁ ≠ b.m₂ ∧ H b.m₁ = H b.m₂

theorem ValidBreak_iff (H : Bytes → Bytes) (b : AggregateBreak) :
    ValidBreak H b ↔ b.m₁ ≠ b.m₂ ∧ H b.m₁ = H b.m₂ :=
  Iff.rfl

/-- A validated break is a `HashCollision` witness of the collision game for `H`. -/
def ValidBreak.toCollision {H : Bytes → Bytes} {b : AggregateBreak} (h : ValidBreak H b) :
    HashCollision H :=
  ⟨b.m₁, b.m₂, h.1, h.2⟩

/-- Every `HashCollision` witness is a validated break. -/
theorem HashCollision.validBreak {H : Bytes → Bytes} (c : HashCollision H) :
    ValidBreak H ⟨c.m₁, c.m₂⟩ :=
  ⟨c.distinct, c.collides⟩

/-- An injective commitment hash admits no validated break. -/
theorem not_validBreak_of_injective {H : Bytes → Bytes}
    (hInj : ∀ a b : Bytes, H a = H b → a = b) (b : AggregateBreak) : ¬ ValidBreak H b :=
  fun h => h.1 (hInj _ _ h.2)

/-- `b` is a break of the experiment with transcript `log`: a collision of `H` both of whose
    inputs are recorded queries. A collision the prover did not query is not one. -/
def TranscriptBreak (H : Bytes → Bytes) (log : List (Bytes × Bytes)) (b : AggregateBreak) : Prop :=
  b.m₁ ∈ log.map Prod.fst ∧ b.m₂ ∈ log.map Prod.fst ∧ ValidBreak H b

theorem TranscriptBreak_iff (H : Bytes → Bytes) (log : List (Bytes × Bytes)) (b : AggregateBreak) :
    TranscriptBreak H log b ↔
      b.m₁ ∈ log.map Prod.fst ∧ b.m₂ ∈ log.map Prod.fst ∧ ValidBreak H b :=
  Iff.rfl

theorem TranscriptBreak.append_left {H : Bytes → Bytes} {log : List (Bytes × Bytes)}
    {b : AggregateBreak} (h : TranscriptBreak H log b) (log' : List (Bytes × Bytes)) :
    TranscriptBreak H (log ++ log') b := by
  refine ⟨?_, ?_, h.2.2⟩
  · rw [List.map_append]; exact List.mem_append_left _ h.1
  · rw [List.map_append]; exact List.mem_append_left _ h.2.1

theorem TranscriptBreak.append_right {H : Bytes → Bytes} {log : List (Bytes × Bytes)}
    {b : AggregateBreak} (h : TranscriptBreak H log b) (log' : List (Bytes × Bytes)) :
    TranscriptBreak H (log' ++ log) b := by
  refine ⟨?_, ?_, h.2.2⟩
  · rw [List.map_append]; exact List.mem_append_right _ h.1
  · rw [List.map_append]; exact List.mem_append_right _ h.2.1

/-- Executable collision search over a transcript: two entries with different queries and the
    same answer. -/
def transcriptCollision (log : List (Bytes × Bytes)) : Bool :=
  log.any (fun e => log.any (fun e' => decide (e.1 ≠ e'.1) && decide (e.2 = e'.2)))

/-- A collision found in a transcript whose answers are those of `H` is a transcript break. -/
theorem transcriptCollision_sound (H : Bytes → Bytes) (log : List (Bytes × Bytes))
    (hLog : ∀ e ∈ log, e.2 = H e.1) (h : transcriptCollision log = true) :
    ∃ b : AggregateBreak, TranscriptBreak H log b := by
  obtain ⟨e, he, h'⟩ := List.any_eq_true.mp h
  obtain ⟨e', he', hc⟩ := List.any_eq_true.mp h'
  obtain ⟨hNe, hEq⟩ := aggAndSplit hc
  refine ⟨⟨e.1, e'.1⟩, List.mem_map.mpr ⟨e, he, rfl⟩, List.mem_map.mpr ⟨e', he', rfl⟩,
    of_decide_eq_true hNe, ?_⟩
  show H e.1 = H e'.1
  rw [← hLog e he, ← hLog e' he']
  exact of_decide_eq_true hEq

/-- Every transcript break is found by the search. -/
theorem transcriptCollision_complete (H : Bytes → Bytes) (log : List (Bytes × Bytes))
    (hLog : ∀ e ∈ log, e.2 = H e.1) {b : AggregateBreak} (h : TranscriptBreak H log b) :
    transcriptCollision log = true := by
  obtain ⟨e, he, he1⟩ := List.mem_map.mp h.1
  obtain ⟨e', he', he1'⟩ := List.mem_map.mp h.2.1
  refine List.any_eq_true.mpr ⟨e, he, List.any_eq_true.mpr ⟨e', he', ?_⟩⟩
  have hNe : e.1 ≠ e'.1 := by rw [he1, he1']; exact h.2.2.1
  have hEq : e.2 = e'.2 := by rw [hLog e he, hLog e' he', he1, he1']; exact h.2.2.2
  rw [decide_eq_true hNe, decide_eq_true hEq]
  rfl

/-- Knowledge-soundness outcome of one accepted aggregate with transcript `log`: the extracted
    witness map is valid, or the transcript contains a collision of `H`. -/
def AggregateSoundnessOutcome {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool) (H : Bytes → Bytes) (log : List (Bytes × Bytes))
    (stmt : AggregateStatement PK w) (extracted : Fin w → Option Sig) : Prop :=
  ValidAggregateWitness verifySingle stmt extracted ∨ ∃ b : AggregateBreak, TranscriptBreak H log b

theorem AggregateSoundnessOutcome_iff {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool) (H : Bytes → Bytes) (log : List (Bytes × Bytes))
    (stmt : AggregateStatement PK w) (extracted : Fin w → Option Sig) :
    AggregateSoundnessOutcome verifySingle H log stmt extracted ↔
      (ValidAggregateWitness verifySingle stmt extracted ∨
        ∃ b : AggregateBreak, TranscriptBreak H log b) :=
  Iff.rfl

theorem AggregateSoundnessOutcome.of_witness {PK Sig : Type} {w : Nat}
    {verifySingle : PK → Bytes → Sig → Bool} {H : Bytes → Bytes} {log : List (Bytes × Bytes)}
    {stmt : AggregateStatement PK w} {extracted : Fin w → Option Sig}
    (h : ValidAggregateWitness verifySingle stmt extracted) :
    AggregateSoundnessOutcome verifySingle H log stmt extracted :=
  .inl h

theorem AggregateSoundnessOutcome.of_break {PK Sig : Type} {w : Nat}
    {verifySingle : PK → Bytes → Sig → Bool} {H : Bytes → Bytes} {log : List (Bytes × Bytes)}
    {stmt : AggregateStatement PK w} {extracted : Fin w → Option Sig}
    (b : AggregateBreak) (h : TranscriptBreak H log b) :
    AggregateSoundnessOutcome verifySingle H log stmt extracted :=
  .inr ⟨b, h⟩

/-- With an injective commitment hash the outcome is a valid extracted witness. -/
theorem AggregateSoundnessOutcome.witness_of_injective {PK Sig : Type} {w : Nat}
    {verifySingle : PK → Bytes → Sig → Bool} {H : Bytes → Bytes} {log : List (Bytes × Bytes)}
    {stmt : AggregateStatement PK w} {extracted : Fin w → Option Sig}
    (hInj : ∀ a b : Bytes, H a = H b → a = b)
    (h : AggregateSoundnessOutcome verifySingle H log stmt extracted) :
    ValidAggregateWitness verifySingle stmt extracted := by
  rcases h with hW | ⟨b, hB⟩
  · exact hW
  · exact absurd hB.2.2 (not_validBreak_of_injective hInj b)

/-- **Accepted aggregate, per signer.** Under the outcome, for every active signer `i` and
    every participation predicate: the transcript contains a collision of `H`, or the extracted
    witness map of this run holds a signature that verifies under signer `i`'s key although `i`
    did not participate, or `i` participated. The second branch names the signature the
    extractor produced from the run; the mere existence of a verifying signature is not in it. -/
theorem AggregateSoundnessOutcome.signer_trichotomy {PK Sig : Type} {w : Nat}
    {verifySingle : PK → Bytes → Sig → Bool} {H : Bytes → Bytes} {log : List (Bytes × Bytes)}
    {stmt : AggregateStatement PK w} {extracted : Fin w → Option Sig}
    (h : AggregateSoundnessOutcome verifySingle H log stmt extracted)
    (participated : Fin w → Bool) (i : Fin w) (hActive : stmt.bitmap.getLsbD i.val = true) :
    (∃ b : AggregateBreak, TranscriptBreak H log b) ∨
    (∃ sig : Sig, extracted i = some sig ∧
      verifySingle (stmt.roster i) stmt.message sig = true ∧ participated i = false) ∨
    participated i = true := by
  rcases h with hW | hB
  · have hi := hW i hActive
    cases hs : extracted i with
    | none => rw [hs] at hi; exact False.elim hi
    | some sig =>
      rw [hs] at hi
      cases hp : participated i with
      | false => exact .inr (.inl ⟨sig, rfl, hi, rfl⟩)
      | true => exact .inr (.inr rfl)
  · exact .inl hB

/-- The second branch is about the extracted map: when the extractor returns nothing for a
    non-participating active signer and the transcript has no collision, the outcome fails,
    even if every signature verifies under every key. -/
theorem aggregateOutcome_rejects_unextracted_signer :
    ¬ AggregateSoundnessOutcome (PK := Unit) (Sig := Unit) (fun _ _ _ => true) (fun m => m)
        [] ⟨fun _ => (), 1#1, []⟩ (fun _ => none) := by
  rintro (hW | ⟨b, hb⟩)
  · exact hW ⟨0, Nat.one_pos⟩ (by decide)
  · exact nomatch hb.1

/-- Soundness outcomes compose along a merge: outcomes for the two children give the outcome
    for the bitwise-OR bitmap with the merged witness map over the concatenated transcript. -/
theorem mergeSoundnessOutcome {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool) (H : Bytes → Bytes)
    (roster : Fin w → PK) (msg : Bytes) (bmL bmR : BitVec w)
    (wL wR : Fin w → Option Sig) (logL logR : List (Bytes × Bytes))
    (hL : AggregateSoundnessOutcome verifySingle H logL ⟨roster, bmL, msg⟩ wL)
    (hR : AggregateSoundnessOutcome verifySingle H logR ⟨roster, bmR, msg⟩ wR) :
    AggregateSoundnessOutcome verifySingle H (logL ++ logR) ⟨roster, bmL ||| bmR, msg⟩
      (mergeWitnessMaps bmL wL wR) := by
  rcases hL with hWL | ⟨b, hb⟩
  · rcases hR with hWR | ⟨b, hb⟩
    · exact .inl (mergeWitnessMaps_valid verifySingle roster msg bmL bmR wL wR hWL hWR)
    · exact .inr ⟨b, hb.append_right logL⟩
  · exact .inr ⟨b, hb.append_left logR⟩

/-- Executable check of `ValidAggregateWitness`. -/
def aggregateWitnessCheck {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (stmt : AggregateStatement PK w) (sigs : Fin w → Option Sig) : Bool :=
  (List.finRange w).all (fun i =>
    !stmt.bitmap.getLsbD i.val ||
      match sigs i with
      | none => false
      | some sig => verifySingle (stmt.roster i) stmt.message sig)

theorem aggregateWitnessCheck_sound {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (stmt : AggregateStatement PK w) (sigs : Fin w → Option Sig)
    (h : aggregateWitnessCheck verifySingle stmt sigs = true) :
    ValidAggregateWitness verifySingle stmt sigs := by
  intro i hBit
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  rw [hBit] at hi
  cases hs : sigs i with
  | none => rw [hs] at hi; cases hi
  | some sig => rw [hs] at hi; exact hi

theorem aggregateWitnessCheck_complete {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (stmt : AggregateStatement PK w) (sigs : Fin w → Option Sig)
    (h : ValidAggregateWitness verifySingle stmt sigs) :
    aggregateWitnessCheck verifySingle stmt sigs = true := by
  apply List.all_eq_true.mpr
  intro i _
  cases hBit : stmt.bitmap.getLsbD i.val with
  | false => rfl
  | true =>
    have hi := h i hBit
    cases hs : sigs i with
    | none => rw [hs] at hi; exact False.elim hi
    | some sig =>
      rw [hs] at hi
      simp only [Bool.not_true, Bool.false_or, hi]

/-- The challenger's recording oracle: the first `q` queries are answered by `H` and logged
    with their answers; later queries are answered `[]` and not logged. -/
def recordingOracle (H : Bytes → Bytes) (q : Nat) (log : List (Bytes × Bytes)) :
    (x : byteOracleIface.Query) → byteOracleIface.Resp x × List (Bytes × Bytes) :=
  fun (x : Bytes) => if log.length < q then (H x, log ++ [(x, H x)]) else ([], log)

/-- One run of a prover against the recording oracle: its output and the transcript. -/
def aggregateRun {PK Proof : Type} {w : Nat} (H : Bytes → Bytes) (q : Nat)
    (prover : Code byteOracleIface (AggregateStatement PK w × Proof)) :
    (AggregateStatement PK w × Proof) × List (Bytes × Bytes) :=
  Code.play (recordingOracle H q) prover []

/-- A single funded call records exactly its input and the answer used to construct the output. -/
theorem aggregateRun_one_call {PK Proof : Type} {w Q : Nat} (hQ : 1 ≤ Q)
    (H : Bytes → Bytes) (x : Bytes) (finish : Bytes → AggregateStatement PK w × Proof) :
    aggregateRun H Q (.call x (fun y => .ret (finish y))) = (finish (H x), [(x, H x)]) := by
  unfold aggregateRun
  rw [Code.play_call, Code.play_ret]
  simp [recordingOracle, show 0 < Q from hQ]

private theorem play_after_budget {R : Type} (H H' : Bytes → Bytes) (Q : Nat)
    (log : List (Bytes × Bytes)) (full : Q ≤ log.length) (prog : Code byteOracleIface R) :
    Code.play (recordingOracle H Q) prog log = Code.play (recordingOracle H' Q) prog log := by
  induction prog with
  | ret v => rw [Code.play_ret, Code.play_ret]
  | call q k ih =>
    simp only [Code.play_call, recordingOracle, Nat.not_lt.mpr full, ↓reduceIte]
    exact ih []

/-- With budget one, a two-valued oracle produces one of the two constant-oracle runs,
    even for an adaptive program that keeps calling after exhausting its budget. -/
theorem aggregateRun_one_two_answers {PK Proof : Type} {w : Nat} (H : Bytes → Bytes) (x y : Bytes)
    (range : ∀ q, H q = x ∨ H q = y) (prog : Code byteOracleIface (AggregateStatement PK w × Proof)) :
    aggregateRun H 1 prog = aggregateRun (fun _ => x) 1 prog ∨
    aggregateRun H 1 prog = aggregateRun (fun _ => y) 1 prog := by
  cases prog with
  | ret v => exact .inl (by simp [aggregateRun, Code.play_ret])
  | call q k =>
    have agree (v : Bytes) (hv : H q = v) :
        aggregateRun H 1 (.call q k) = aggregateRun (fun _ => v) 1 (.call q k) := by
      simp only [aggregateRun, Code.play_call, recordingOracle, List.length_nil,
        Nat.zero_lt_succ, ↓reduceIte, List.nil_append, hv]
      exact play_after_budget H _ 1 [(q, v)] (Nat.le_refl 1) (k v)
    exact (range q).imp (agree x) (agree y)

theorem transcriptCollision_singleton (x y : Bytes) : transcriptCollision [(x, y)] = false := by
  simp [transcriptCollision]

/-- Every transcript entry is a query with the answer of `H`, and at most `q` are recorded. -/
theorem aggregateRun_log {PK Proof : Type} {w : Nat} (H : Bytes → Bytes) (q : Nat)
    (prover : Code byteOracleIface (AggregateStatement PK w × Proof)) :
    (∀ e ∈ (aggregateRun H q prover).2, e.2 = H e.1) ∧ (aggregateRun H q prover).2.length ≤ q :=
  Code.play_invariant (recordingOracle H q)
    (fun log => (∀ e ∈ log, e.2 = H e.1) ∧ log.length ≤ q)
    (fun log (x : Bytes) h => by
      if hc : log.length < q then
        have hEq : recordingOracle H q log x = (H x, log ++ [(x, H x)]) := aggItePos hc _ _
        rw [hEq]
        refine ⟨fun e he => ?_, ?_⟩
        · rcases List.mem_append.mp he with hOld | hNew
          · exact h.1 e hOld
          · rcases List.mem_cons.mp hNew with hHead | hNil
            · rw [hHead]
            · exact nomatch hNil
        · show (log ++ [(x, H x)]).length ≤ q
          rw [List.length_append]
          exact hc
      else
        have hEq : recordingOracle H q log x = ([], log) := aggIteNeg hc _ _
        rw [hEq]
        exact h)
    prover []
    (show (∀ e ∈ ([] : List (Bytes × Bytes)), e.2 = H e.1) ∧
        ([] : List (Bytes × Bytes)).length ≤ q from
      ⟨fun _ h => (nomatch h), Nat.zero_le q⟩)

/-- The prover's winning condition on one run: the verifier accepts, the extracted witness map
    is not valid, and the transcript contains no collision. -/
def aggregateFailure {PK Sig Proof : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (H : Bytes → Bytes) (r : (AggregateStatement PK w × Proof) × List (Bytes × Bytes)) : Bool :=
  verifyAgg H r.1.1 r.1.2 &&
    (!aggregateWitnessCheck verifySingle r.1.1 (extract r.2 r.1.1 r.1.2) && !transcriptCollision r.2)

/-- **Knowledge-soundness game.** On coin `ω` the oracle is `oracle ω`, the prover `prover ω`
    runs against the recording oracle with budget `q`, and the prover wins when
    `aggregateFailure` holds of the run. -/
def aggregateSoundnessGame {PK Sig Proof : Type} {w n : Nat} (hPos : 0 < n)
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (q : Nat) (oracle : Fin n → Bytes → Bytes)
    (prover : Fin n → Code byteOracleIface (AggregateStatement PK w × Proof)) : FinGame n :=
  ⟨hPos, fun ω => aggregateFailure verifySingle verifyAgg extract (oracle ω)
    (aggregateRun (oracle ω) q (prover ω))⟩

/-- A winning coin gives an accepted statement and an invalid extracted witness. -/
theorem aggregateSoundnessGame_win_invalid {PK Sig Proof : Type} {w n : Nat} (hPos : 0 < n)
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (q : Nat) (oracle : Fin n → Bytes → Bytes)
    (prover : Fin n → Code byteOracleIface (AggregateStatement PK w × Proof)) (ω : Fin n)
    (h : (aggregateSoundnessGame hPos verifySingle verifyAgg extract q oracle prover).win ω = true) :
    let r := aggregateRun (oracle ω) q (prover ω)
    verifyAgg (oracle ω) r.1.1 r.1.2 = true ∧
      ¬ ValidAggregateWitness verifySingle r.1.1 (extract r.2 r.1.1 r.1.2) := by
  simp only [aggregateSoundnessGame, aggregateFailure, Bool.and_eq_true] at h
  exact ⟨h.1, fun hw => by
    have hf := h.2.1
    rw [aggregateWitnessCheck_complete verifySingle _ _ hw] at hf
    contradiction⟩

/-- On a run the prover does not win and the verifier accepts, the outcome holds: the
    extracted witness map is valid or the transcript contains a collision of the oracle. -/
theorem aggregateFailure_false_outcome {PK Sig Proof : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (H : Bytes → Bytes) (q : Nat)
    (prover : Code byteOracleIface (AggregateStatement PK w × Proof))
    (hLose : aggregateFailure verifySingle verifyAgg extract H (aggregateRun H q prover) = false)
    (hAcc : verifyAgg H (aggregateRun H q prover).1.1 (aggregateRun H q prover).1.2 = true) :
    AggregateSoundnessOutcome verifySingle H (aggregateRun H q prover).2
      (aggregateRun H q prover).1.1
      (extract (aggregateRun H q prover).2 (aggregateRun H q prover).1.1
        (aggregateRun H q prover).1.2) := by
  have hF := hLose
  unfold aggregateFailure at hF
  rw [hAcc, Bool.true_and] at hF
  cases hW : aggregateWitnessCheck verifySingle (aggregateRun H q prover).1.1
      (extract (aggregateRun H q prover).2 (aggregateRun H q prover).1.1
        (aggregateRun H q prover).1.2) with
  | true => exact .inl (aggregateWitnessCheck_sound verifySingle _ _ hW)
  | false =>
    rw [hW] at hF
    cases hC : transcriptCollision (aggregateRun H q prover).2 with
    | true => exact .inr (transcriptCollision_sound H _ (aggregateRun_log H q prover).1 hC)
    | false =>
      rw [hC] at hF
      cases hF

/-- A run on which the verifier accepts and the outcome fails is a win of the prover. -/
theorem aggregateFailure_of_no_outcome {PK Sig Proof : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (H : Bytes → Bytes) (q : Nat)
    (prover : Code byteOracleIface (AggregateStatement PK w × Proof))
    (hAcc : verifyAgg H (aggregateRun H q prover).1.1 (aggregateRun H q prover).1.2 = true)
    (hNot : ¬ AggregateSoundnessOutcome verifySingle H (aggregateRun H q prover).2
      (aggregateRun H q prover).1.1
      (extract (aggregateRun H q prover).2 (aggregateRun H q prover).1.1
        (aggregateRun H q prover).1.2)) :
    aggregateFailure verifySingle verifyAgg extract H (aggregateRun H q prover) = true := by
  cases hG : aggregateFailure verifySingle verifyAgg extract H (aggregateRun H q prover) with
  | true => rfl
  | false =>
    exact absurd (aggregateFailure_false_outcome verifySingle verifyAgg extract H q prover hG hAcc)
      hNot

/-- **Straight-line extractors.** Every signature the extractor returns is carried by the proof
    (`proofSigs proof`) or is the decoding, by the fixed decoder `decode`, of a recorded query or
    answer. Such an extractor cannot return a signature it found by searching `Sig` with
    `verifySingle`: the decoder sees one byte string and neither the statement nor the keys. -/
def StraightLineExtractor {PK Sig Proof : Type} {w : Nat}
    (decode : Bytes → Option Sig) (proofSigs : Proof → List Sig)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig) :
    Prop :=
  ∀ (log : List (Bytes × Bytes)) (stmt : AggregateStatement PK w) (proof : Proof) (i : Fin w)
    (sig : Sig), extract log stmt proof i = some sig →
    sig ∈ proofSigs proof ∨ ∃ e ∈ log, decode e.1 = some sig ∨ decode e.2 = some sig

theorem StraightLineExtractor_iff {PK Sig Proof : Type} {w : Nat}
    (decode : Bytes → Option Sig) (proofSigs : Proof → List Sig)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig) :
    StraightLineExtractor decode proofSigs extract ↔
      ∀ (log : List (Bytes × Bytes)) (stmt : AggregateStatement PK w) (proof : Proof) (i : Fin w)
        (sig : Sig), extract log stmt proof i = some sig →
        sig ∈ proofSigs proof ∨ ∃ e ∈ log, decode e.1 = some sig ∨ decode e.2 = some sig :=
  Iff.rfl

/-- **Knowledge-soundness contract** of the aggregate verifier `verifyAgg` with extractor
    `extract` of the class `ℰ`, for the oracle family `oracle` sampled by the challenger, prover
    query budget `q` and error `ε`: the extractor belongs to `ℰ`, and every prover, reading only
    its own coin and the oracle's answers, makes the verifier accept without a valid extracted
    witness and without a transcript collision with probability at most `ε`.

    The class `ℰ` is where a restriction on extractors lives. With the unrestricted class the
    contract does not express soundness on satisfiable statements
    (`acceptAll_alwaysValid_unrestricted_extractorSound`); `StraightLineExtractor` is a class
    for which it does (`acceptAll_not_straightLine_extractorSound`).

    The oracle family is an index. A family the prover can predict (a constant one) gives a
    contract only verifiers that need no oracle satisfy with small `ε`; the intended instance
    is a family in which the answers at different queries are independent. In `Qsag.Top.Aggregation`,
    this contract is instantiated with `StraightLineExtractor` for the non-transparent 256-column
    `StepOp` AIR committee verifier via `stepOp256TableOk_xmss_extract`, while succinct WHIR/Canopy
    compilation factors through `Qsag.Top.ClosedProtocolReductions`. -/
@[expose] def AggregateExtractorSound {PK Sig Proof : Type} {w nC : Nat}
    (ℰ : (List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig) → Prop)
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (oracle : Fin nC → Bytes → Bytes) (q : Nat) (ε : RatBound) : Prop :=
  ℰ extract ∧
  ∀ (n nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA)
    (prover : Fin nA → Code byteOracleIface (AggregateStatement PK w × Proof)),
    GameBound (aggregateSoundnessGame hPos verifySingle verifyAgg extract q
      (fun ω => oracle (π.chal ω)) (fun ω => prover (π.advc ω))).winProb ε

section Contract
variable {PK Sig Proof : Type} {w nC : Nat}
  {ℰ : (List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig) → Prop}
  {verifySingle : PK → Bytes → Sig → Bool}
  {verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool}
  {extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig}
  {oracle : Fin nC → Bytes → Bytes} {q : Nat} {ε : RatBound}

/-- **Explicit bound.** For every prover, any event contained in "the verifier accepts, the
    extracted witness map is not valid and the transcript has no collision of the oracle" has
    probability at most `ε`. -/
theorem AggregateExtractorSound.failure_bound
    (C : AggregateExtractorSound ℰ verifySingle verifyAgg extract oracle q ε)
    {n nA : Nat} (hPos : 0 < n) (π : CoinSplit n nC nA)
    (prover : Fin nA → Code byteOracleIface (AggregateStatement PK w × Proof))
    (fail : Fin n → Bool)
    (hFail : ∀ ω : Fin n, fail ω = true →
      verifyAgg (oracle (π.chal ω))
        (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
        (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 = true ∧
      ¬ AggregateSoundnessOutcome verifySingle (oracle (π.chal ω))
        (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2
        (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
        (extract (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2
          (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
          (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2)) :
    GameBound (FinGame.mk hPos fail).winProb ε :=
  GameBound.trans
    (event_le_reduction_win (FinGame.mk hPos fail)
      (aggregateSoundnessGame hPos verifySingle verifyAgg extract q
        (fun ω => oracle (π.chal ω)) (fun ω => prover (π.advc ω)))
      (fun ω hF => aggregateFailure_of_no_outcome verifySingle verifyAgg extract
        (oracle (π.chal ω)) q (prover (π.advc ω)) (hFail ω hF).1 (hFail ω hF).2))
    (C.2 n nA hPos π prover)

/-- The contract weakens along the bound. -/
theorem AggregateExtractorSound.mono {ε' : RatBound}
    (C : AggregateExtractorSound ℰ verifySingle verifyAgg extract oracle q ε) (hLe : ε.le ε') :
    AggregateExtractorSound ℰ verifySingle verifyAgg extract oracle q ε' :=
  ⟨C.1, fun n nA hPos π prover => GameBound.trans (C.2 n nA hPos π prover) hLe⟩

end Contract

/-- Construct `StraightLineExtractor` from a proof-carried witness list `proofSigs`. -/
theorem StraightLineExtractor.of_proofSigs {PK Sig Proof : Type} {w : Nat}
    (decode : Bytes → Option Sig) (proofSigs : Proof → List Sig)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (hMem : ∀ log stmt proof i sig, extract log stmt proof i = some sig → sig ∈ proofSigs proof) :
    StraightLineExtractor decode proofSigs extract :=
  fun log stmt proof i sig hs => .inl (hMem log stmt proof i sig hs)

/-- Construct zero-error `AggregateExtractorSound` from deterministic extraction soundness on
    every accepted proof (or recorded transcript collision). -/
theorem AggregateExtractorSound.of_deterministic {PK Sig Proof : Type} {w nC : Nat}
    (ℰ : (List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig) → Prop)
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (hℰ : ℰ extract) (oracle : Fin nC → Bytes → Bytes) (q : Nat)
    (hSound : ∀ (H : Bytes → Bytes) (log : List (Bytes × Bytes))
      (stmt : AggregateStatement PK w) (proof : Proof),
      (∀ e ∈ log, e.2 = H e.1) →
      verifyAgg H stmt proof = true →
      AggregateSoundnessOutcome verifySingle H log stmt (extract log stmt proof)) :
    AggregateExtractorSound ℰ verifySingle verifyAgg extract oracle q RatBound.zero := by
  refine ⟨hℰ, fun n nA hPos π prover => FinGame.bound_zero_of_forall_lose _ (fun ω => ?_)⟩
  let H := oracle (π.chal ω)
  let r := aggregateRun H q (prover (π.advc ω))
  show aggregateFailure verifySingle verifyAgg extract H r = false
  unfold aggregateFailure
  cases hAcc : verifyAgg H r.1.1 r.1.2 with
  | false => rfl
  | true =>
    rw [Bool.true_and]
    rcases hSound H r.2 r.1.1 r.1.2 (aggregateRun_log H q (prover (π.advc ω))).1 hAcc with
      hWit | ⟨b, hb⟩
    · rw [aggregateWitnessCheck_complete verifySingle r.1.1 _ hWit]
      rfl
    · rw [transcriptCollision_complete H r.2 (aggregateRun_log H q (prover (π.advc ω))).1 hb,
        Bool.not_true, Bool.and_false]

/-- With `ε = 1` the contract holds for every verifier, every extractor of the class and every
    oracle family: it carries no information. -/
theorem aggregateExtractorSound_one {PK Sig Proof : Type} {w nC : Nat}
    (ℰ : (List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig) → Prop)
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (hℰ : ℰ extract) (oracle : Fin nC → Bytes → Bytes) (q : Nat) :
    AggregateExtractorSound ℰ verifySingle verifyAgg extract oracle q RatBound.one :=
  ⟨hℰ, fun _ _ _ _ _ => FinGame.winProb_le_one _⟩

/-- **Transparent control.** The aggregate whose proof is the signature map itself, checked
    signature by signature, is knowledge sound with error `0` and a straight-line extractor:
    the extractor reads the witness off the proof. It is not succinct and uses no oracle; it
    shows that the contract is satisfiable with a small bound by a verifier that does check. -/
theorem transparentAggregate_extractorSound {PK Sig : Type} {w nC : Nat}
    (verifySingle : PK → Bytes → Sig → Bool) (oracle : Fin nC → Bytes → Bytes) (q : Nat) :
    AggregateExtractorSound
      (StraightLineExtractor (fun _ => none)
        (fun proof : Fin w → Option Sig => (List.finRange w).filterMap proof))
      verifySingle
      (fun _ stmt (proof : Fin w → Option Sig) => aggregateWitnessCheck verifySingle stmt proof)
      (fun _ _ proof => proof) oracle q RatBound.zero := by
  refine ⟨fun _ _ proof i sig hs =>
    .inl (List.mem_filterMap.mpr ⟨i, List.mem_finRange i, hs⟩), ?_⟩
  intro n nA hPos π prover
  refine FinGame.bound_zero_of_forall_lose _ (fun ω => ?_)
  show (aggregateWitnessCheck verifySingle
      (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
      (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 &&
    (!aggregateWitnessCheck verifySingle
      (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
      (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 &&
      !transcriptCollision (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2)) = false
  cases aggregateWitnessCheck verifySingle
      (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
      (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 <;> rfl

/-- **The unrestricted extractor class does not express soundness.** When every signature
    verifies under every key, the accept-all verifier satisfies the contract with error `0`
    for the unrestricted class: the extractor that returns a signature for every validator,
    looking at nothing, is always right. A contract stated for `fun _ => True` says nothing
    about a verifier on statements that have a witness. -/
theorem acceptAll_alwaysValid_unrestricted_extractorSound {PK Proof : Type} {w nC : Nat}
    (oracle : Fin nC → Bytes → Bytes) (q : Nat) :
    AggregateExtractorSound (PK := PK) (Sig := Unit) (Proof := Proof) (w := w) (fun _ => True)
      (fun _ _ _ => true) (fun _ _ _ => true) (fun _ _ _ _ => some ()) oracle q
      RatBound.zero := by
  refine ⟨trivial, ?_⟩
  intro n nA hPos π prover
  refine FinGame.bound_zero_of_forall_lose _ (fun ω => ?_)
  have hCheck : aggregateWitnessCheck (PK := PK) (Sig := Unit) (fun _ _ _ => true)
      (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1 (fun _ => some ()) = true :=
    List.all_eq_true.mpr (fun _ _ => Bool.or_true _)
  show (true && (!aggregateWitnessCheck (PK := PK) (Sig := Unit) (fun _ _ _ => true)
      (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1 (fun _ => some ()) &&
    !transcriptCollision (aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2)) = false
  rw [hCheck]
  rfl

/-! ## Rejected instances -/

/-- **The accept-all verifier is not knowledge sound on an unsatisfiable statement.** For every
    extractor of any class, every oracle
    family (injective or not, predictable or not) and every query budget: if some statement has
    no valid witness, the verifier that accepts everything satisfies the contract for no
    `ε < 1`. The prover outputs that statement and asks nothing, so no transcript collision can
    excuse the extractor. -/
theorem acceptAll_not_extractorSound {PK Sig Proof : Type} {w nC : Nat} (hPos : 0 < nC)
    (verifySingle : PK → Bytes → Sig → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (oracle : Fin nC → Bytes → Bytes) (q : Nat)
    (stmt : AggregateStatement PK w) (proof : Proof)
    (hUnsat : ∀ sigs : Fin w → Option Sig, aggregateWitnessCheck verifySingle stmt sigs = false)
    (ℰ : (List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig) → Prop)
    {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ AggregateExtractorSound ℰ verifySingle (fun _ _ _ => true) extract oracle q ε := by
  intro h
  refine FinGame.not_bound_of_forall_win _ (fun ω => ?_) hε
    (h.2 nC 1 hPos (CoinSplit.challengerOnly nC) (fun _ => .ret (stmt, proof)))
  have hRun : aggregateRun (oracle ((CoinSplit.challengerOnly nC).chal ω)) q
      (Code.ret (stmt, proof) : Code byteOracleIface (AggregateStatement PK w × Proof)) =
      ((stmt, proof), []) := Code.play_ret _ _ _
  show aggregateFailure verifySingle (fun _ _ _ => true) extract
    (oracle ((CoinSplit.challengerOnly nC).chal ω))
    (aggregateRun (oracle ((CoinSplit.challengerOnly nC).chal ω)) q (Code.ret (stmt, proof))) = true
  rw [hRun]
  show (true && (!aggregateWitnessCheck verifySingle stmt (extract [] stmt proof) &&
    !transcriptCollision [])) = true
  rw [hUnsat]
  rfl

/-- A statement naming one signer under a single-signature verifier that rejects everything
    has no valid witness. -/
theorem rejectAll_statement_unsatisfiable (sigs : Fin 1 → Option Unit) :
    aggregateWitnessCheck (PK := Unit) (fun _ _ _ => false) ⟨fun _ => (), 1#1, []⟩ sigs = false := by
  cases hc : aggregateWitnessCheck (PK := Unit) (Sig := Unit) (fun _ _ _ => false)
      ⟨fun _ => (), 1#1, []⟩ sigs with
  | false => rfl
  | true =>
    have hi := aggregateWitnessCheck_sound _ _ _ hc ⟨0, Nat.one_pos⟩ (by decide)
    cases hs : sigs ⟨0, Nat.one_pos⟩ with
    | none => rw [hs] at hi; exact False.elim hi
    | some sig => rw [hs] at hi; exact Bool.noConfusion hi

/-- The first audit's instance: one signer, no valid signature, a verifier that accepts. No
    extractor, oracle family or bound `ε < 1` makes it knowledge sound. -/
theorem acceptAll_unit_not_extractorSound {nC : Nat} (hPos : 0 < nC)
    (extract : List (Bytes × Bytes) → AggregateStatement Unit 1 → Unit → Fin 1 → Option Unit)
    (oracle : Fin nC → Bytes → Bytes) (q : Nat)
    (ℰ : (List (Bytes × Bytes) → AggregateStatement Unit 1 → Unit → Fin 1 → Option Unit) → Prop)
    {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ AggregateExtractorSound ℰ (fun _ _ _ => false) (fun _ _ _ => true) extract oracle q ε :=
  acceptAll_not_extractorSound hPos _ extract oracle q ⟨fun _ => (), 1#1, []⟩ ()
    rejectAll_statement_unsatisfiable ℰ hε

/-- **The accept-all verifier is not knowledge sound for straight-line extractors**, whether or
    not the statement has a valid witness. For every single-signature verifier, decoder,
    extractor, oracle family and budget: given a statement with an active signer and a proof
    carrying no signature, the prover outputs them and asks nothing; a straight-line extractor
    then has nothing to return, so the contract holds for no `ε < 1`. -/
theorem acceptAll_not_straightLine_extractorSound {PK Sig Proof : Type} {w nC : Nat}
    (hPos : 0 < nC) (verifySingle : PK → Bytes → Sig → Bool)
    (decode : Bytes → Option Sig) (proofSigs : Proof → List Sig)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (oracle : Fin nC → Bytes → Bytes) (q : Nat)
    (stmt : AggregateStatement PK w) (proof : Proof) (i : Fin w)
    (hActive : stmt.bitmap.getLsbD i.val = true) (hEmpty : proofSigs proof = [])
    {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ AggregateExtractorSound (StraightLineExtractor decode proofSigs) verifySingle
        (fun _ _ _ => true) extract oracle q ε := by
  intro h
  refine FinGame.not_bound_of_forall_win _ (fun ω => ?_) hε
    (h.2 nC 1 hPos (CoinSplit.challengerOnly nC) (fun _ => .ret (stmt, proof)))
  have hRun : aggregateRun (oracle ((CoinSplit.challengerOnly nC).chal ω)) q
      (Code.ret (stmt, proof) : Code byteOracleIface (AggregateStatement PK w × Proof)) =
      ((stmt, proof), []) := Code.play_ret _ _ _
  have hCheck : aggregateWitnessCheck verifySingle stmt (extract [] stmt proof) = false := by
    cases hc : aggregateWitnessCheck verifySingle stmt (extract [] stmt proof) with
    | false => rfl
    | true =>
      have hi := aggregateWitnessCheck_sound verifySingle _ _ hc i hActive
      cases hs : extract [] stmt proof i with
      | none => rw [hs] at hi; exact False.elim hi
      | some sig =>
        rcases h.1 [] stmt proof i sig hs with hIn | ⟨e, he, _⟩
        · rw [hEmpty] at hIn
          exact nomatch hIn
        · exact nomatch he
  show aggregateFailure verifySingle (fun _ _ _ => true) extract
    (oracle ((CoinSplit.challengerOnly nC).chal ω))
    (aggregateRun (oracle ((CoinSplit.challengerOnly nC).chal ω)) q (Code.ret (stmt, proof))) = true
  rw [hRun]
  show (true && (!aggregateWitnessCheck verifySingle stmt (extract [] stmt proof) &&
    !transcriptCollision [])) = true
  rw [hCheck]
  rfl

/-- The referee's instance: every signature verifies and the verifier accepts everything. For
    a straight-line extractor over proofs that carry no signature, no oracle family and no
    `ε < 1` make it knowledge sound. -/
theorem acceptAll_alwaysValid_not_straightLine_extractorSound {nC : Nat} (hPos : 0 < nC)
    (decode : Bytes → Option Unit)
    (extract : List (Bytes × Bytes) → AggregateStatement Unit 1 → Unit → Fin 1 → Option Unit)
    (oracle : Fin nC → Bytes → Bytes) (q : Nat) {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ AggregateExtractorSound (StraightLineExtractor decode (fun _ : Unit => []))
        (fun _ _ _ => true) (fun _ _ _ => true) extract oracle q ε :=
  acceptAll_not_straightLine_extractorSound hPos _ decode _ extract oracle q
    ⟨fun _ => (), 1#1, []⟩ () ⟨0, Nat.one_pos⟩ (by decide) rfl hε

/-- A collision of `H` outside the transcript is not a break of the experiment: with the
    constant hash and an empty transcript, the colliding pair `([0], [1])` does not discharge
    the outcome. -/
theorem aggregateOutcome_rejects_unqueried_collision :
    ¬ AggregateSoundnessOutcome (PK := Unit) (Sig := Unit) (fun _ _ _ => false) (fun _ => [])
        [] ⟨fun _ => (), 1#1, []⟩ (fun _ => some ()) := by
  rintro (hW | ⟨b, hb⟩)
  · have h := hW ⟨0, Nat.one_pos⟩ (by decide)
    exact Bool.noConfusion h
  · exact nomatch hb.1

/-! ## §5. Canonical Ideal Aggregation State Machine & `DataRefines` Bridges -/

/-- Ideal aggregation functionality `idealAggregateMachine`: maintains the monotonic list of
    certified `AggregateStatement`s and accepts `(stmt, sigs)` iff `aggregateWitnessCheck` holds
    for every active validator in `stmt.bitmap`. -/
def idealAggregateMachine {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool) :
    Machine (List (AggregateStatement PK w))
      (AggregateStatement PK w × (Fin w → Option Sig)) Unit where
  Init log := log = []
  step log inp :=
    if aggregateWitnessCheck verifySingle inp.1 inp.2 then
      some (log ++ [inp.1], ())
    else
      none
  errStep log _ := log

theorem idealAggregateMachine_accepts_witness {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool) (log : List (AggregateStatement PK w))
    (stmt : AggregateStatement PK w) (sigs : Fin w → Option Sig)
    (h : ValidAggregateWitness verifySingle stmt sigs) :
    (idealAggregateMachine verifySingle).step log (stmt, sigs) = some (log ++ [stmt], ()) := by
  simp [idealAggregateMachine, aggregateWitnessCheck_complete verifySingle stmt sigs h]

#verify_constructive idealAggregateMachine_accepts_witness

/-- **Reachable-Trace Soundness of `idealAggregateMachine` (`idealAggregateMachine_all_certified_valid`)**:
    Along every multi-turn trace from the empty log, every certified statement recorded in the ideal
    state possesses a valid witness map supplying individual signatures for all active validators. -/
theorem idealAggregateMachine_all_certified_valid {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    {tr : List ((AggregateStatement PK w × (Fin w → Option Sig)) × Unit)}
    {log : List (AggregateStatement PK w)}
    (hTrace : (idealAggregateMachine verifySingle).ValidTrace [] tr log) :
    ∀ stmt ∈ log, ∃ sigs : Fin w → Option Sig, ValidAggregateWitness verifySingle stmt sigs := by
  have hInv : ∀ {s₀ s : List (AggregateStatement PK w)}
      {t : List ((AggregateStatement PK w × (Fin w → Option Sig)) × Unit)},
      (idealAggregateMachine verifySingle).ValidTrace s₀ t s →
      (∀ st ∈ s₀, ∃ sigs, ValidAggregateWitness verifySingle st sigs) →
      ∀ st ∈ s, ∃ sigs, ValidAggregateWitness verifySingle st sigs := by
    intro s₀ s t hT
    induction hT with
    | nil => exact fun h0 => h0
    | accept hStep _ ih =>
      intro h0
      dsimp only [idealAggregateMachine] at hStep
      cases hChk : aggregateWitnessCheck verifySingle _ _ with
      | false => rw [hChk] at hStep; cases hStep
      | true =>
        rw [hChk] at hStep
        injection hStep with hPair
        obtain ⟨hNext, _⟩ := Prod.mk.inj hPair
        subst hNext
        refine ih (fun st hMem => ?_)
        rcases List.mem_append.mp hMem with hOld | hSingle
        · exact h0 st hOld
        · rcases List.mem_cons.mp hSingle with rfl | hEmpty
          · exact ⟨_, aggregateWitnessCheck_sound verifySingle _ _ hChk⟩
          · exact nomatch hEmpty
    | reject _ _ _ ih => exact ih
  exact hInv hTrace (fun _ h => nomatch h)

/-- Concrete verifier state tracking accepted statements alongside an audit counter of rejected
    submissions (`abs s := s.accepted` is non-injective). -/
structure VerifiedAggregateState (PK : Type) (w : Nat) where
  accepted : List (AggregateStatement PK w)
  rejectedCount : Nat

/-- Submission to a concrete aggregate verifier carrying `(stmt, proof, log)`. -/
structure AggregateSubmission (PK Proof : Type) (w : Nat) where
  stmt : AggregateStatement PK w
  proof : Proof
  log : List (Bytes × Bytes)

/-- Concrete succinct verifier machine guarded outside the explicitly bounded bad events
    (`aggregateFailure` and `transcriptCollision`). -/
def verifiedAggregateMachine {PK Sig Proof : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (H : Bytes → Bytes) :
    Machine (VerifiedAggregateState PK w) (AggregateSubmission PK Proof w) Unit where
  Init s := s.accepted = [] ∧ s.rejectedCount = 0
  step s sub :=
    if verifyAgg H sub.stmt sub.proof &&
       !aggregateFailure verifySingle verifyAgg extract H ((sub.stmt, sub.proof), sub.log) &&
       !transcriptCollision sub.log then
      some ({ s with accepted := s.accepted ++ [sub.stmt] }, ())
    else
      none
  errStep s _ := { s with rejectedCount := s.rejectedCount + 1 }

/-- Visibility projection extracting `(stmt, extract log stmt proof)` for `idealAggregateMachine`. -/
def verifiedAggregateVisIn {PK Sig Proof : Type} {w : Nat}
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (sub : AggregateSubmission PK Proof w) :
    Option (AggregateStatement PK w × (Fin w → Option Sig)) :=
  some (sub.stmt, extract sub.log sub.stmt sub.proof)

/-- **Forward Simulation (`verifiedAggregate_dataRefines_ideal`)**:
    Outside the bounded knowledge-extraction and transcript-collision bad events, any concrete
    aggregate verifier `verifyAgg` refines `idealAggregateMachine verifySingle` via `DataRefines`
    with non-identity state abstraction `VerifiedAggregateState.accepted`. -/
def verifiedAggregate_dataRefines_ideal {PK Sig Proof : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (H : Bytes → Bytes) :
    DataRefines
      (verifiedAggregateMachine verifySingle verifyAgg extract H)
      (idealAggregateMachine verifySingle)
      (verifiedAggregateVisIn extract)
      id where
  Rel c a := c.accepted = a
  absInit c₀ := c₀.accepted
  init_ok {c₀} hInit := ⟨hInit.1, rfl⟩
  sim_visible {c c' a sub out j} hRel hStepC hVis := by
    subst hRel
    injection hVis with hJ
    subst hJ
    dsimp only [verifiedAggregateMachine] at hStepC
    cases hVer : verifyAgg H sub.stmt sub.proof with
    | false => rw [hVer] at hStepC; cases hStepC
    | true =>
      cases hW : aggregateWitnessCheck verifySingle sub.stmt (extract sub.log sub.stmt sub.proof) with
      | true =>
        cases hColl : transcriptCollision sub.log with
        | true =>
          have hGuard :
              (true && !aggregateFailure verifySingle verifyAgg extract H
                ((sub.stmt, sub.proof), sub.log) && !true) = false := by
            simp
          rw [hVer, hColl] at hStepC
          simp at hStepC
        | false =>
          have hFailFalse :
              aggregateFailure verifySingle verifyAgg extract H ((sub.stmt, sub.proof), sub.log) = false := by
            unfold aggregateFailure
            rw [hVer, hW, hColl]
            rfl
          rw [hVer, hFailFalse, hColl] at hStepC
          injection hStepC with hPair
          obtain ⟨hC, hO⟩ := Prod.mk.inj hPair
          subst hC; subst hO
          refine ⟨c.accepted ++ [sub.stmt], ?_, rfl⟩
          dsimp only [idealAggregateMachine]
          rw [hW]
          rfl
      | false =>
        cases hColl : transcriptCollision sub.log with
        | true =>
          rw [hVer, hColl] at hStepC
          simp at hStepC
        | false =>
          have hFailTrue :
              aggregateFailure verifySingle verifyAgg extract H ((sub.stmt, sub.proof), sub.log) = true := by
            unfold aggregateFailure
            rw [hVer, hW, hColl]
            rfl
          rw [hVer, hFailTrue] at hStepC
          cases hStepC
  sim_internal {_ _ _ _ _} _ _ hVis := by cases hVis
  sim_reject {c a _} hRel _ := hRel

/-- Unfiltered concrete aggregate verifier machine running `verifyAgg H sub.stmt sub.proof` directly. -/
def rawAggregateVerifierMachine {PK Proof : Type} {w : Nat}
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (H : Bytes → Bytes) :
    Machine (VerifiedAggregateState PK w) (AggregateSubmission PK Proof w) Unit where
  Init s := s.accepted = [] ∧ s.rejectedCount = 0
  step s sub :=
    if verifyAgg H sub.stmt sub.proof then
      some ({ s with accepted := s.accepted ++ [sub.stmt] }, ())
    else
      none
  errStep s _ := { s with rejectedCount := s.rejectedCount + 1 }

/-- **Unfiltered Forward Simulation (`unconditionalAggregate_dataRefines_ideal`)**:
    Whenever `verifyAgg H stmt proof = true` unconditionally implies `ValidAggregateWitness` on
    `extract log stmt proof` (as proved for the 256-column `StepOp` AIR verifier via
    `stepOp256TableOk_xmss_extract`), `rawAggregateVerifierMachine verifyAgg H` refines
    `idealAggregateMachine verifySingle` directly with zero bad-event filtering! -/
def unconditionalAggregate_dataRefines_ideal {PK Sig Proof : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (verifyAgg : (Bytes → Bytes) → AggregateStatement PK w → Proof → Bool)
    (extract : List (Bytes × Bytes) → AggregateStatement PK w → Proof → Fin w → Option Sig)
    (H : Bytes → Bytes)
    (hSound : ∀ (stmt : AggregateStatement PK w) (proof : Proof) (log : List (Bytes × Bytes)),
      verifyAgg H stmt proof = true →
      ValidAggregateWitness verifySingle stmt (extract log stmt proof)) :
    DataRefines
      (rawAggregateVerifierMachine verifyAgg H)
      (idealAggregateMachine verifySingle)
      (verifiedAggregateVisIn extract)
      id where
  Rel c a := c.accepted = a
  absInit c₀ := c₀.accepted
  init_ok {c₀} hInit := ⟨hInit.1, rfl⟩
  sim_visible {c c' a sub out j} hRel hStepC hVis := by
    subst hRel
    injection hVis with hJ
    subst hJ
    dsimp only [rawAggregateVerifierMachine] at hStepC
    cases hVer : verifyAgg H sub.stmt sub.proof with
    | false => rw [hVer] at hStepC; cases hStepC
    | true =>
      rw [hVer] at hStepC
      injection hStepC with hPair
      obtain ⟨hC, hO⟩ := Prod.mk.inj hPair
      subst hC; subst hO
      have hChk : aggregateWitnessCheck verifySingle sub.stmt
          (extract sub.log sub.stmt sub.proof) = true :=
        aggregateWitnessCheck_complete verifySingle _ _ (hSound sub.stmt sub.proof sub.log hVer)
      refine ⟨c.accepted ++ [sub.stmt], ?_, rfl⟩
      dsimp only [idealAggregateMachine]
      rw [hChk]
      rfl
  sim_internal {_ _ _ _ _} _ _ hVis := by cases hVis
  sim_reject {c a _} hRel _ := hRel

/-- **`#tooth` Unsound Verifier Breaks `idealAggregateMachine` (`tooth_unsound_verifier_breaks_idealAggregate`)**:
    Running `rawAggregateVerifierMachine` with an accept-all verifier admits an unsatisfiable
    1-validator statement into `accepted`, which no `ValidTrace` of `idealAggregateMachine` from `[]`
    can ever reach! -/
theorem tooth_unsound_verifier_breaks_idealAggregate :
    ∃ (sub : AggregateSubmission Unit Unit 1) (s' : VerifiedAggregateState Unit 1),
      (rawAggregateVerifierMachine (PK := Unit) (Proof := Unit) (w := 1)
        (fun _ _ _ => true) (fun b => b)).Init ⟨[], 0⟩ ∧
      (rawAggregateVerifierMachine (PK := Unit) (Proof := Unit) (w := 1)
        (fun _ _ _ => true) (fun b => b)).step ⟨[], 0⟩ sub = some (s', ()) ∧
      ¬ ∃ tr : List ((AggregateStatement Unit 1 × (Fin 1 → Option Unit)) × Unit),
        (idealAggregateMachine (PK := Unit) (Sig := Unit) (fun _ _ _ => false)).ValidTrace
          [] tr s'.accepted := by
  let badStmt : AggregateStatement Unit 1 := ⟨fun _ => (), 1#1, []⟩
  refine ⟨⟨badStmt, (), []⟩, ⟨[badStmt], 0⟩, ⟨rfl, rfl⟩, rfl, ?_⟩
  rintro ⟨tr, hTr⟩
  obtain ⟨sigs, hValid⟩ := idealAggregateMachine_all_certified_valid
    (fun _ _ _ => false) hTr badStmt (.head _)
  have hChk := aggregateWitnessCheck_complete (fun _ _ _ => false) badStmt sigs hValid
  rw [rejectAll_statement_unsatisfiable sigs] at hChk
  cases hChk

#tooth_pair AggregateExtractorSound.failure_bound vs acceptAll_not_extractorSound
#tooth_pair aggregateExtractorSound_one vs acceptAll_unit_not_extractorSound
#tooth_pair transparentAggregate_extractorSound vs acceptAll_unit_not_extractorSound
#tooth_pair mergeSoundnessOutcome vs aggregateOutcome_rejects_unqueried_collision
#tooth_pair acceptAll_alwaysValid_unrestricted_extractorSound vs acceptAll_alwaysValid_not_straightLine_extractorSound
#tooth_pair transparentAggregate_extractorSound vs acceptAll_not_straightLine_extractorSound
#tooth_pair AggregateSoundnessOutcome.signer_trichotomy vs aggregateOutcome_rejects_unextracted_signer
#tooth_pair idealAggregateMachine_all_certified_valid vs tooth_unsound_verifier_breaks_idealAggregate

#verify_constructive Qsag.Spec.mergeWitnessMaps_valid
#verify_constructive Qsag.Spec.HashCollision.validBreak
#verify_constructive Qsag.Spec.not_validBreak_of_injective
#verify_constructive Qsag.Spec.TranscriptBreak.append_left
#verify_constructive Qsag.Spec.TranscriptBreak.append_right
#verify_constructive Qsag.Spec.transcriptCollision_sound
#verify_constructive Qsag.Spec.transcriptCollision_complete
#verify_constructive Qsag.Spec.AggregateSoundnessOutcome.witness_of_injective
#verify_constructive Qsag.Spec.AggregateSoundnessOutcome.signer_trichotomy
#verify_constructive Qsag.Spec.mergeSoundnessOutcome
#verify_constructive Qsag.Spec.aggregateWitnessCheck_sound
#verify_constructive Qsag.Spec.aggregateWitnessCheck_complete
#verify_constructive aggregateRun_one_call play_after_budget aggregateRun_one_two_answers transcriptCollision_singleton
#verify_constructive Qsag.Spec.aggregateRun_log
#verify_constructive Qsag.Spec.aggregateSoundnessGame_win_invalid
#verify_constructive Qsag.Spec.aggregateFailure_false_outcome
#verify_constructive Qsag.Spec.aggregateFailure_of_no_outcome
#verify_constructive Qsag.Spec.AggregateExtractorSound.failure_bound
#verify_constructive Qsag.Spec.AggregateExtractorSound.mono
#verify_constructive Qsag.Spec.aggregateExtractorSound_one
#verify_constructive Qsag.Spec.transparentAggregate_extractorSound
#verify_constructive Qsag.Spec.acceptAll_not_extractorSound
#verify_constructive Qsag.Spec.rejectAll_statement_unsatisfiable
#verify_constructive Qsag.Spec.acceptAll_unit_not_extractorSound
#verify_constructive Qsag.Spec.aggregateOutcome_rejects_unqueried_collision
#verify_constructive Qsag.Spec.aggregateOutcome_rejects_unextracted_signer
#verify_constructive Qsag.Spec.acceptAll_alwaysValid_unrestricted_extractorSound
#verify_constructive Qsag.Spec.acceptAll_not_straightLine_extractorSound
#verify_constructive Qsag.Spec.acceptAll_alwaysValid_not_straightLine_extractorSound
#verify_constructive Qsag.Spec.ValidAggregateWitness_iff
#verify_constructive Qsag.Spec.ValidAggregateWitness.intro
#verify_constructive Qsag.Spec.ValidBreak_iff
#verify_constructive Qsag.Spec.TranscriptBreak_iff
#verify_constructive Qsag.Spec.AggregateSoundnessOutcome_iff
#verify_constructive Qsag.Spec.AggregateSoundnessOutcome.of_witness
#verify_constructive Qsag.Spec.AggregateSoundnessOutcome.of_break
#verify_constructive Qsag.Spec.StraightLineExtractor_iff
#verify_constructive Qsag.Spec.StraightLineExtractor.of_proofSigs
#verify_constructive Qsag.Spec.AggregateExtractorSound.of_deterministic
#verify_constructive Qsag.Spec.idealAggregateMachine_all_certified_valid
#verify_constructive Qsag.Spec.tooth_unsound_verifier_breaks_idealAggregate

end Qsag.Spec
end

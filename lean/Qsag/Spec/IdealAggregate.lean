module
/-
# Qsag.Spec.IdealAggregate — Ideal Succinct Signature Aggregation Specification

Layer-0 ideal specification for succinct post-quantum signature aggregation and binary merge trees:
1. Public `AggregateStatement` binding roster public keys, signer bitmap `B`, and message digest,
2. Exact witness validity (`ValidAggregateWitness`: every set bit `i` in `B` carries a valid
   individual signature `verify (pks i) msg (sigs i) = true`),
3. Inductive binary `AggregateMergeTree` verifying hierarchical shard-proof composition with
   disjoint signer bitmaps (`b₁ &&& b₂ = 0`), and
4. Knowledge-extraction soundness contract (`AggregateExtractorSound`): on every execution on
   which the aggregate verifier accepts and the soundness-error event does not occur, the
   extractor's witness map is valid or the break finder returns a collision of the commitment
   hash (`ValidBreak`); the soundness-error event has probability at most `εSound`.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
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

/-! ## Knowledge soundness: validated breaks and the extractor contract -/

/-- Break data an aggregate extractor may return: a candidate collision of the commitment hash. -/
structure AggregateBreak where
  m₁ : Bytes
  m₂ : Bytes
  deriving DecidableEq, Repr

/-- `b` is a collision of the commitment hash `H`: two different inputs with the same digest. -/
def ValidBreak (H : Bytes → Bytes) (b : AggregateBreak) : Prop :=
  b.m₁ ≠ b.m₂ ∧ H b.m₁ = H b.m₂

/-- A validated break is a `HashCollision` witness of the collision game for `H`. -/
def ValidBreak.toCollision {H : Bytes → Bytes} {b : AggregateBreak} (h : ValidBreak H b) :
    HashCollision H :=
  ⟨b.m₁, b.m₂, h.1, h.2⟩

/-- Every `HashCollision` witness is a validated break. -/
theorem HashCollision.validBreak {H : Bytes → Bytes} (c : HashCollision H) :
    ValidBreak H ⟨c.m₁, c.m₂⟩ :=
  ⟨c.distinct, c.collides⟩

/-- Executable validity check of a break. -/
def validBreakCheck (H : Bytes → Bytes) (b : AggregateBreak) : Bool :=
  decide (b.m₁ ≠ b.m₂) && decide (H b.m₁ = H b.m₂)

theorem validBreakCheck_iff (H : Bytes → Bytes) (b : AggregateBreak) :
    validBreakCheck H b = true ↔ ValidBreak H b := by
  unfold validBreakCheck ValidBreak
  constructor
  · intro h
    cases h₁ : decide (b.m₁ ≠ b.m₂) with
    | false => rw [h₁] at h; cases h
    | true =>
      rw [h₁, Bool.true_and] at h
      exact ⟨of_decide_eq_true h₁, of_decide_eq_true h⟩
  · rintro ⟨h₁, h₂⟩
    rw [decide_eq_true h₁, decide_eq_true h₂]
    rfl

/-- An injective commitment hash admits no validated break. -/
theorem not_validBreak_of_injective {H : Bytes → Bytes}
    (hInj : ∀ a b : Bytes, H a = H b → a = b) (b : AggregateBreak) : ¬ ValidBreak H b :=
  fun h => h.1 (hInj _ _ h.2)

/-- Knowledge-soundness outcome for one accepted aggregate: the extracted witness map satisfies
    `ValidAggregateWitness`, or the break finder returned a validated collision of `H`. -/
def AggregateSoundnessOutcome {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool) (H : Bytes → Bytes)
    (stmt : AggregateStatement PK w)
    (extracted : Fin w → Option Sig)
    (brk : Option AggregateBreak) : Prop :=
  ValidAggregateWitness verifySingle stmt extracted ∨ ∃ b : AggregateBreak, brk = some b ∧ ValidBreak H b

/-- With an injective commitment hash the outcome is a valid extracted witness. -/
theorem AggregateSoundnessOutcome.witness_of_injective {PK Sig : Type} {w : Nat}
    {verifySingle : PK → Bytes → Sig → Bool} {H : Bytes → Bytes}
    {stmt : AggregateStatement PK w} {extracted : Fin w → Option Sig}
    {brk : Option AggregateBreak}
    (hInj : ∀ a b : Bytes, H a = H b → a = b)
    (h : AggregateSoundnessOutcome verifySingle H stmt extracted brk) :
    ValidAggregateWitness verifySingle stmt extracted := by
  rcases h with hW | ⟨b, _, hB⟩
  · exact hW
  · exact absurd hB (not_validBreak_of_injective hInj b)

/-- Break returned for a merged aggregate: the left break if it validates, else the right. -/
def mergeBreaks (H : Bytes → Bytes) (l r : Option AggregateBreak) : Option AggregateBreak :=
  match l with
  | some b => if validBreakCheck H b = true then some b else r
  | none => r

/-- Soundness outcomes compose along a merge: outcomes for the two children give the outcome
    for the bitwise-OR bitmap with the merged witness map and the merged break. -/
theorem mergeSoundnessOutcome {PK Sig : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool) (H : Bytes → Bytes)
    (roster : Fin w → PK) (msg : Bytes) (bmL bmR : BitVec w)
    (wL wR : Fin w → Option Sig) (brkL brkR : Option AggregateBreak)
    (hL : AggregateSoundnessOutcome verifySingle H ⟨roster, bmL, msg⟩ wL brkL)
    (hR : AggregateSoundnessOutcome verifySingle H ⟨roster, bmR, msg⟩ wR brkR) :
    AggregateSoundnessOutcome verifySingle H ⟨roster, bmL ||| bmR, msg⟩
      (mergeWitnessMaps bmL wL wR) (mergeBreaks H brkL brkR) := by
  have hOfRight : (∃ b : AggregateBreak, brkR = some b ∧ ValidBreak H b) →
      ∃ b : AggregateBreak, mergeBreaks H brkL brkR = some b ∧ ValidBreak H b := by
    rintro ⟨b, hb, hV⟩
    unfold mergeBreaks
    cases brkL with
    | none => exact ⟨b, hb, hV⟩
    | some bl =>
      cases hc : validBreakCheck H bl with
      | true =>
        refine ⟨bl, ?_, (validBreakCheck_iff H bl).mp hc⟩
        show (if validBreakCheck H bl = true then some bl else brkR) = some bl
        rw [hc]
        rfl
      | false =>
        refine ⟨b, ?_, hV⟩
        show (if validBreakCheck H bl = true then some bl else brkR) = some b
        rw [hc]
        exact hb
  rcases hL with hWL | ⟨bl, hbl, hVl⟩
  · rcases hR with hWR | hBR
    · exact .inl (mergeWitnessMaps_valid verifySingle roster msg bmL bmR wL wR hWL hWR)
    · exact .inr (hOfRight hBR)
  · refine .inr ⟨bl, ?_, hVl⟩
    rw [hbl]
    show (if validBreakCheck H bl = true then some bl else brkR) = some bl
    rw [(validBreakCheck_iff H bl).mpr hVl]
    rfl

/-- One execution of the aggregate soundness experiment: the statement and proof output by the
    prover and the extractor's view of that prover (its oracle queries and committed data). -/
structure AggregateRun (PK Proof View : Type) (w : Nat) where
  stmt : AggregateStatement PK w
  proof : Proof
  view : View

/-- **Knowledge-soundness contract** of the aggregate verifier `verifyAgg` against the prover
    whose executions over the coin space `Fin n` are `run`.

    `extract` and `findBreak` are functions of the extractor's view alone. On every coin on
    which `verifyAgg` accepts and the soundness-error event `bad` does not occur, the outcome
    is a valid extracted witness or a validated collision of `H`; `bad` has probability at most
    `εSound`. -/
structure AggregateExtractorSound {PK Sig Proof View : Type} {w n : Nat}
    (verifySingle : PK → Bytes → Sig → Bool) (H : Bytes → Bytes)
    (verifyAgg : AggregateStatement PK w → Proof → Bool)
    (run : Fin n → AggregateRun PK Proof View w) where
  samplePos : 0 < n
  extract : View → Fin w → Option Sig
  findBreak : View → Option AggregateBreak
  bad : Fin n → Bool
  εSound : RatBound
  accepted_outcome : ∀ ω : Fin n,
    verifyAgg (run ω).stmt (run ω).proof = true → bad ω = false →
    AggregateSoundnessOutcome verifySingle H (run ω).stmt (extract (run ω).view)
      (findBreak (run ω).view)
  bad_bound : GameBound (FinGame.mk samplePos bad).winProb εSound

/-- Any event contained in "the verifier accepts and the outcome fails" has probability at most
    `εSound`. -/
theorem AggregateExtractorSound.failure_bound {PK Sig Proof View : Type} {w n : Nat}
    {verifySingle : PK → Bytes → Sig → Bool} {H : Bytes → Bytes}
    {verifyAgg : AggregateStatement PK w → Proof → Bool}
    {run : Fin n → AggregateRun PK Proof View w}
    (C : AggregateExtractorSound verifySingle H verifyAgg run)
    (fail : Fin n → Bool)
    (hFail : ∀ ω : Fin n, fail ω = true →
      verifyAgg (run ω).stmt (run ω).proof = true ∧
      ¬ AggregateSoundnessOutcome verifySingle H (run ω).stmt (C.extract (run ω).view)
        (C.findBreak (run ω).view)) :
    GameBound (FinGame.mk C.samplePos fail).winProb C.εSound := by
  refine GameBound.trans
    (event_le_reduction_win (FinGame.mk C.samplePos fail) (FinGame.mk C.samplePos C.bad) ?_)
    C.bad_bound
  intro ω hF
  obtain ⟨hAcc, hNot⟩ := hFail ω hF
  cases hb : C.bad ω with
  | true => exact hb
  | false => exact absurd (C.accepted_outcome ω hAcc hb) hNot

/-- With an injective commitment hash, every accepted aggregate outside the soundness-error
    event has a valid extracted witness. -/
theorem AggregateExtractorSound.accepted_extracts_of_injective
    {PK Sig Proof View : Type} {w n : Nat}
    {verifySingle : PK → Bytes → Sig → Bool} {H : Bytes → Bytes}
    {verifyAgg : AggregateStatement PK w → Proof → Bool}
    {run : Fin n → AggregateRun PK Proof View w}
    (C : AggregateExtractorSound verifySingle H verifyAgg run)
    (hInj : ∀ a b : Bytes, H a = H b → a = b) (ω : Fin n)
    (hAcc : verifyAgg (run ω).stmt (run ω).proof = true) (hGood : C.bad ω = false) :
    ValidAggregateWitness verifySingle (run ω).stmt (C.extract (run ω).view) :=
  (C.accepted_outcome ω hAcc hGood).witness_of_injective hInj

/-- **Accepted aggregate, per signer.** On a coin where the verifier accepts outside the
    soundness-error event, for every active signer `i` and every participation predicate:
    the break finder returned a validated collision of `H`, or some signature verifies under
    signer `i`'s key although `i` did not participate (a forgery against `i`), or `i`
    participated. -/
theorem AggregateExtractorSound.accepted_signer_trichotomy
    {PK Sig Proof View : Type} {w n : Nat}
    {verifySingle : PK → Bytes → Sig → Bool} {H : Bytes → Bytes}
    {verifyAgg : AggregateStatement PK w → Proof → Bool}
    {run : Fin n → AggregateRun PK Proof View w}
    (C : AggregateExtractorSound verifySingle H verifyAgg run)
    (participated : Fin w → Bool) (ω : Fin n)
    (hAcc : verifyAgg (run ω).stmt (run ω).proof = true) (hGood : C.bad ω = false)
    (i : Fin w) (hActive : (run ω).stmt.bitmap.getLsbD i.val = true) :
    (∃ b : AggregateBreak, C.findBreak (run ω).view = some b ∧ ValidBreak H b) ∨
    (∃ sig : Sig, verifySingle ((run ω).stmt.roster i) (run ω).stmt.message sig = true ∧
      participated i = false) ∨
    participated i = true := by
  rcases C.accepted_outcome ω hAcc hGood with hW | hB
  · have hi := hW i hActive
    cases hs : C.extract (run ω).view i with
    | none => rw [hs] at hi; exact False.elim hi
    | some sig =>
      rw [hs] at hi
      cases hp : participated i with
      | false => exact .inr (.inl ⟨sig, hi, rfl⟩)
      | true => exact .inr (.inr rfl)
  · exact .inl hB

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

/-- The contract is satisfiable: the aggregate whose proof is the signature map itself, checked
    signature by signature, is knowledge sound with the identity extractor and an empty
    soundness-error event. -/
def transparentAggregate_extractorSound {PK Sig : Type} {w n : Nat} (hPos : 0 < n)
    (verifySingle : PK → Bytes → Sig → Bool) (H : Bytes → Bytes)
    (run : Fin n → AggregateRun PK (Fin w → Option Sig) (Fin w → Option Sig) w)
    (hView : ∀ ω : Fin n, (run ω).view = (run ω).proof) :
    AggregateExtractorSound verifySingle H (aggregateWitnessCheck verifySingle) run where
  samplePos := hPos
  extract := fun view => view
  findBreak := fun _ => none
  bad := fun _ => false
  εSound := (FinGame.mk hPos (fun _ => false)).winProb
  accepted_outcome := fun ω hAcc _ => .inl (by
    rw [hView ω]
    exact aggregateWitnessCheck_sound verifySingle (run ω).stmt (run ω).proof hAcc)
  bad_bound := GameBound.refl _

/-- A returned pair that is not a collision does not discharge the outcome: with a verifier
    that rejects every individual signature, an active signer and the identity hash, the pair
    `([0], [1])` leaves the outcome false. -/
theorem aggregateOutcome_rejects_unvalidated_break :
    ¬ AggregateSoundnessOutcome (PK := Unit) (Sig := Unit) (fun _ _ _ => false) (fun m => m)
        ⟨fun _ => (), 1#1, []⟩ (fun _ => some ()) (some ⟨[0], [1]⟩) := by
  rintro (hW | ⟨b, hb, hV⟩)
  · have h := hW ⟨0, Nat.one_pos⟩ (by decide)
    exact Bool.noConfusion h
  · cases hb
    exact absurd hV.2 (by decide)

#tooth_pair AggregateExtractorSound.failure_bound vs aggregateOutcome_rejects_unvalidated_break
#tooth_pair mergeSoundnessOutcome vs aggregateOutcome_rejects_unvalidated_break

#verify_constructive
  Qsag.Spec.mergeWitnessMaps_valid
  Qsag.Spec.HashCollision.validBreak
  Qsag.Spec.validBreakCheck_iff
  Qsag.Spec.not_validBreak_of_injective
  Qsag.Spec.AggregateSoundnessOutcome.witness_of_injective
  Qsag.Spec.mergeSoundnessOutcome
  Qsag.Spec.AggregateExtractorSound.failure_bound
  Qsag.Spec.AggregateExtractorSound.accepted_extracts_of_injective
  Qsag.Spec.AggregateExtractorSound.accepted_signer_trichotomy
  Qsag.Spec.aggregateWitnessCheck_sound
  Qsag.Spec.aggregateOutcome_rejects_unvalidated_break

end Qsag.Spec
end

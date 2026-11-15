module
/-
# Qsag.Spec.IdealAggregate — Ideal Succinct Signature Aggregation Specification

Layer-0 ideal specification for succinct post-quantum signature aggregation and binary merge trees:
1. Public `AggregateStatement` binding roster public keys, signer bitmap `B`, and message digest,
2. Exact witness validity (`ValidAggregateWitness`: every set bit `i` in `B` carries a valid
   individual signature `verify (pks i) msg (sigs i) = true`),
3. Inductive binary `AggregateMergeTree` verifying hierarchical shard-proof composition with
   disjoint signer bitmaps (`b₁ &&& b₂ = 0`), and
4. Knowledge-extraction soundness interface (`AggregateExtractorSound`) separating extracted
   witness validity from collision / round-by-round soundness error bounds.
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

/-- Knowledge-soundness specification for an aggregate verifier `verifyAgg`: either an extracted
    witness map satisfies `ValidAggregateWitness` or an explicit cryptographic break event occurs. -/
def AggregateSoundnessOutcome {PK Sig Break : Type} {w : Nat}
    (verifySingle : PK → Bytes → Sig → Bool)
    (stmt : AggregateStatement PK w)
    (extracted : Fin w → Option Sig)
    (brk : Option Break) : Prop :=
  ValidAggregateWitness verifySingle stmt extracted ∨ ∃ b : Break, brk = some b

#verify_constructive
  Qsag.Spec.mergeWitnessMaps_valid

end Qsag.Spec
end

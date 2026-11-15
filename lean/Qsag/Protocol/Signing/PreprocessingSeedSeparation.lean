module
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Signing.HashSigs
public section
namespace Qsag.PreprocessingGame
/-! ## Production signature/Merkle seed encoding connection

`thNodeH` feeds `pkSeed` into the self-delimiting `thPreimage`. Distinct seed slices
are disjoint inputs, proved below, but the implementation does not generate a new
uniform challenge seed for each call. Disjoint encoding is not freshness.
-/

def nodeRequest (seed : List UInt8) (adrs : HashAdrs) (left right : List UInt8) : List UInt8 :=
  thPreimage tagThH seed adrs [left, right]

theorem nodeRequest_seed_separation {seed₁ seed₂ : List UInt8}
    (adrs₁ adrs₂ : HashAdrs) (left₁ right₁ left₂ right₂ : List UInt8)
    (different : seed₁ ≠ seed₂) :
    nodeRequest seed₁ adrs₁ left₁ right₁ ≠ nodeRequest seed₂ adrs₂ left₂ right₂ := by
  intro same
  exact different (thPreimage_injective same).2.1

theorem nodeRequest_is_production (suite : TweakableHashSuite) (seed : List UInt8)
    (adrs : HashAdrs) (left right : List UInt8) :
    thNodeH suite seed adrs left right = suite.rawHash (nodeRequest seed adrs left right) := by
  unfold thNodeH thCall nodeRequest
  rfl

/-- Concrete reduction output: distinct accepted node pairs give the two actual
encoded raw-hash inputs, not merely a proposition that a collision exists. -/
def nodeCollisionWitness (suite : TweakableHashSuite) (seed : List UInt8) (adrs : HashAdrs)
    (left right : List UInt8 × List UInt8) (hne : left ≠ right)
    (heq : thNodeH suite seed adrs left.1 left.2 = thNodeH suite seed adrs right.1 right.2) :
    HashCollisionWitness suite.rawHash where
  m1 := nodeRequest seed adrs left.1 left.2
  m2 := nodeRequest seed adrs right.1 right.2
  ne := by
    intro same
    have args := (thPreimage_injective same).2.2.2
    have hl := (List.cons.inj args).1
    have hr := (List.cons.inj (List.cons.inj args).2).1
    exact hne (Prod.ext hl hr)
  eq := by simpa only [nodeRequest_is_production] using heq

/-- Production public-key derivation preserves the supplied seed; it does not sample
fresh salt. Any fresh-key preprocessing theorem must account for key generation upstream. -/
theorem production_seed_is_preserved (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) : (derivePublicKey suite params sk).pkSeed = sk.pkSeed := rfl

/-- The fresh-salt table theorem applies to encoded production node requests for any
finite collection of candidate seeds. No distributional claim about the real keygen
is introduced: the experiment explicitly samples the seed index after preprocessing. -/
theorem freshSalt_node_requests_bound {k : Nat}
    (seeds : Fin k → List UInt8) (suite : TweakableHashSuite) (adrs : HashAdrs)
    (table : List (Fin k × ((List UInt8 × List UInt8) × (List UInt8 × List UInt8)))) :
    qsum k (tableWin (fun salt pair => decide
      (pair.1 ≠ pair.2 ∧
        thNodeH suite (seeds salt) adrs pair.1.1 pair.1.2 =
        thNodeH suite (seeds salt) adrs pair.2.1 pair.2.2)) table) ≤ table.length :=
  freshSalt_table_bound _ _


end Qsag.PreprocessingGame

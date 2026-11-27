module
public import QsagWhirVerified.Fp5Equality
public import QsagWhirVerified.RowPolynomial
public import QsagWhirVerifiedChallengeDefs
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs

abbrev fp5AtBytes (bytes : List U8) (off : Nat) : Option Fp5 :=
  let w := fun k => lePackU64At bytes (off + k)
  let v : Fp5 := ⟨w 0, w 8, w 16, w 24, w 32⟩
  if off + 40 ≤ bytes.length ∧ IsCanonicalFp5 v then some v else none

@[expose] def rowLagrangeWeight : Nat → U64
  | 0 | 8 => 877958875724369725#u64
  | 1 | 7 => 11423073063619626521#u64
  | 2 | 6 => 6136104450867767979#u64
  | 3 | 5 => 6174535167679048363#u64
  | _ => 6116889092462127787#u64

/-- The third component is the product of all node factors visited so far.
The second accumulates the Lagrange numerator of the prefix. -/
@[expose] def rowLagrangeStep (bytes : List U8) (off i : Nat) (claim r : Fp5)
    (first sum product : Fp5) : Option (Fp5 × Fp5 × Fp5) := do
  let v ← fp5AtBytes bytes (off + 40 * i)
  if i = 1 ∧ fp5Add first v ≠ claim then none else
    let factor := fp5Sub r (fp5FromBase (UScalar.ofNat .U64 i))
    some (if i = 0 then v else first,
      fp5Add (fp5Mul sum factor) (fp5Mul product (fp5Scale v (rowLagrangeWeight i))),
      fp5Mul product factor)

@[expose] def rowLagrangeRounds (bytes : List U8) (off : Nat) (claim r : Fp5) :
    Nat → Nat → Fp5 → Fp5 → Fp5 → Option Fp5
  | 0, _, _, sum, _ => some sum
  | n+1, i, first, sum, product => do
    let (f, s, p) ← rowLagrangeStep bytes off i claim r first sum product
    rowLagrangeRounds bytes off claim r n (i+1) f s p


/-- Extend the opened prefix by replacing the unopened subtree containing the
next leaf. Its branching bit is the highest bit that differs from its predecessor. -/
@[expose] def steinerSuffix (limit : Nat) (prev count : Nat) : List Usize → Nat × Bool
  | [] => (count, true)
  | x :: xs =>
    if prev < x.val ∧ x.val < limit ∧ 0 < count then
      steinerSuffix limit x.val (count - 1 + (prev ^^^ x.val).log2) xs
    else (count, false)

abbrev steinerCount (depth : Nat) (leaves : List Usize) : Option Usize := do
  let x :: xs := leaves | none
  if depth > 28 ∨ x.val ≥ 2^depth then none else
    let (n, valid) := steinerSuffix (2^depth) x.val depth xs
    if valid then some (UScalar.ofNat .Usize n) else none


@[expose] def rowChain (bytes : List U8) (off : Nat) (claim : Fp5) : List Fp5 → Option Fp5
  | [] => some claim
  | r :: rest => do
    let next ← rowLagrangeRounds bytes off claim r 9 0 fp5Zero fp5Zero fp5One
    rowChain bytes (off + 360) next rest

end qsag_whir_verified.proofs
end

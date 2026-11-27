module
public import Qsag.Math.QuinticExt5
public section
namespace qsag_whir_verified.proofs

/-- Division-free Lagrange evaluation on the integer grid. After incorporating
node i the numerator is the weighted sum of the samples seen so far, each
multiplied by the product of the other node factors in that prefix. -/
@[expose] def rowGridRounds (sample : Nat → Option Qsag.QuinticGoldilocks)
    (weight : Nat → Qsag.Goldilocks) (claim r : Qsag.QuinticGoldilocks) :
    Nat → Nat → Qsag.QuinticGoldilocks → Qsag.QuinticGoldilocks →
    Qsag.QuinticGoldilocks → Option Qsag.QuinticGoldilocks
  | 0, _, _, sum, _ => some sum
  | n+1, i, first, sum, prod => do
    let v ← sample i
    if i = 1 ∧ Qsag.QuinticGoldilocks.add first v ≠ claim then none else
      let factor := Qsag.QuinticGoldilocks.sub r (Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.ofNat i))
      rowGridRounds sample weight claim r n (i+1) (if i = 0 then v else first)
        (Qsag.QuinticGoldilocks.add (Qsag.QuinticGoldilocks.mul sum factor)
          (Qsag.QuinticGoldilocks.mul prod
            (Qsag.QuinticGoldilocks.mul v (Qsag.QuinticGoldilocks.ofBase (weight i)))))
        (Qsag.QuinticGoldilocks.mul prod factor)


@[expose] def rowGridChain (sample : Nat → Option Qsag.QuinticGoldilocks)
    (weight : Nat → Qsag.Goldilocks) (off : Nat) (claim : Qsag.QuinticGoldilocks) :
    List Qsag.QuinticGoldilocks → Option Qsag.QuinticGoldilocks
  | [] => some claim
  | r :: rest => do
    let next ← rowGridRounds (fun j => sample (off + 40*j)) weight claim r 9 0
      Qsag.QuinticGoldilocks.zero Qsag.QuinticGoldilocks.zero Qsag.QuinticGoldilocks.one
    rowGridChain sample weight (off+360) next rest

end qsag_whir_verified.proofs
end

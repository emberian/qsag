module
public import Qsag.Math.GoldilocksBase
/-
# Qsag.Tests.QipmTeeth — teeth and executed controls for the two-way ideal permutation model

Each tooth is a refutation or an explicit attack paired with the security statement it bites.
The toy game on `Fin 4` is executed by the kernel.
-/
public import Qsag.Oracle.TwoWayQipmCompression
public import Qsag.Oracle.Poseidon2
public import Qsag.Math.Goldilocks

public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## Unweighted inversion collapse -/

/-- Without feed-forward and without a capacity constraint, a one-inverse-query adversary wins
    the preimage game with the full weight, over every state space and every truncation. -/
theorem tooth_qipm_no_feedforward_no_capacity_inverted {D G : Type} [DecidableEq D]
    [DecidableEq G] (elems : List D) (out : D → G) (zs : D) :
    ∃ A : TwoWayQipmAdv D D,
      qipmWeight elems (qipmPreimageWin (fun _ => true) (fun _ z => out z) (out zs))
        (qipmFinalizeFwd A) (1 + 1) [] = qipmFall elems.length 0 (1 + 1) :=
  ⟨TwoWayQipmAdv.inv zs TwoWayQipmAdv.done,
    qipm_unweighted_inverse_attack_total elems out (out zs) zs rfl⟩

/-- The inverse fiber hypothesis of the preimage bound fails for the unprotected truncation:
    the fiber is the whole state space, not `|lane|^2`. -/
theorem tooth_qipm_unprotected_fiber_exceeds_lane_square (l4 : List Lane4)
    (h1 : 1 < l4.length) (z : Poseidon2State12) :
    ¬ (qipmCount (qipmStatesOf l4) (fun x => true && decide (qipmTruncComp x z = z.b0)) ≤
      l4.length * l4.length) := by
  rw [qipm_unprotected_inverse_fiber_full]
  intro h
  have h2 : l4.length * l4.length * l4.length ≤ l4.length * l4.length * 1 := by
    rw [Nat.mul_one]; exact h
  have h3 := Nat.le_of_mul_le_mul_left h2 (Nat.mul_pos (Nat.lt_of_succ_lt h1) (Nat.lt_of_succ_lt h1))
  omega

/-- The real `poseidon2Perm12` with the truncation digest and no input constraint is not
    collision resistant: `poseidon2Perm12Inv` produces explicit collisions. -/
theorem tooth_poseidon2_unweighted_truncation_not_injective :
    ¬ (∀ s t : Poseidon2State12,
      qipmTruncComp s (poseidon2Perm12 s) = qipmTruncComp t (poseidon2Perm12 t) → s = t) := by
  intro h
  have hc := poseidon2_unweighted_truncation_collides
    ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
    ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
    ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
    ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
    (fun e => absurd (congrArg (fun l : Lane4 => l.x0.val) e)
      (show ¬ Goldilocks.zero.val = Goldilocks.one.val by decide))
  exact hc.1 (h _ _ hc.2)

/-! ## Executed toy game on `Fin 4` -/

def qipmToyElems : List (Fin 4) := [0, 1, 2, 3]

theorem qipmToyElems_enum : QipmEnum qipmToyElems := by
  intro a
  revert a
  decide

def qipmToyInvAttack : TwoWayQipmAdv (Fin 4) (Fin 4) :=
  TwoWayQipmAdv.inv 0 TwoWayQipmAdv.done

/-- Identity digest, no constraint: the inverse attack has weight `12 = 4 * 3`, the total. -/
theorem qipm_toy_unprotected_attack_certain :
    qipmWeight qipmToyElems (qipmPreimageWin (fun _ => true) (fun _ z => z) (0 : Fin 4))
      (qipmFinalizeFwd qipmToyInvAttack) 2 [] = 12 ∧ qipmFall qipmToyElems.length 0 2 = 12 := by
  decide +kernel

/-- Feed-forward `x + z`: the same attack keeps weight `3` of `12`. -/
theorem qipm_toy_feed_forward_attack_weight :
    qipmWeight qipmToyElems (qipmPreimageWin (fun _ => true) (fun x z => x + z) (0 : Fin 4))
      (qipmFinalizeFwd qipmToyInvAttack) 2 [] = 3 := by
  decide +kernel

theorem tooth_qipm_toy_feed_forward_defeats_inverse_attack :
    ¬ (qipmWeight qipmToyElems (qipmPreimageWin (fun _ => true) (fun x z => x + z) (0 : Fin 4))
      (qipmFinalizeFwd qipmToyInvAttack) 2 [] = qipmFall qipmToyElems.length 0 2) := by
  decide +kernel

/-- The preimage bound applies to the toy feed-forward compression with fiber count `1`:
    every one-query adversary succeeds with probability at most `2 / 3`. -/
theorem qipm_toy_feed_forward_bound_applies (A : TwoWayQipmAdv (Fin 4) (Fin 4)) :
    RatBound.le (qipmPreimageProb qipmToyElems (fun _ => true) (fun x z => x + z) (0 : Fin 4) A 1
        (by decide))
      ⟨(1 + 1) * 1, qipmToyElems.length - (1 + 1) + 1, Nat.succ_pos _⟩ :=
  qipm_two_way_preimage_bound qipmToyElems qipmToyElems_enum (fun _ => true)
    (fun x z => x + z) 0 1 (by decide) (by decide) A 1 (by decide)

/-- A two-forward-query adaptive adversary stays in budget and the certain event has the full
    weight: the weights are a probability distribution. -/
theorem qipm_toy_total_weight :
    qipmWeight qipmToyElems (fun _ (_ : Fin 4) => true)
      (TwoWayQipmAdv.fwd 1 (fun z => TwoWayQipmAdv.inv z (fun x => TwoWayQipmAdv.done x)))
      2 [] = qipmFall qipmToyElems.length 0 2 := by
  decide +kernel

/-! ## Transposition changes the marked points -/

/-- At a marked point the oracles of `π` and `π ∘ (a b)` really differ. -/
theorem tooth_qipm_swap_changes_marked_point :
    ¬ (qipmPermOracle (n := 2) (w := 1) (fun x => qipmFinSwap 0 1 x) (fun y => qipmFinSwap 0 1 y)
        (fun x => BitVec.ofNat 1 x.val) (qipmFwdIdx 0) =
      qipmPermOracle (n := 2) (w := 1) (fun x => x) (fun y => y)
        (fun x => BitVec.ofNat 1 x.val) (qipmFwdIdx 0)) := by
  decide +kernel

/-! ## Budget shapes -/

/-- The collision (BHT) shape does not meet `2^-128` at `2^56` queries for a 256-bit digest. -/
theorem tooth_qipm_bht_shape_256_fails_at_2pow56 :
    ¬ atLeastBits 128 (qipmBhtShape (2 ^ 56) 256) := by
  decide +kernel

/-- The classical collision bound expression stops meeting `2^-128` beyond `2^64` queries. -/
theorem tooth_qipm_collision_bound_shape_fails_at_2pow65 :
    ¬ atLeastBits 128 ⟨(2 ^ 65 + 2) * ((2 ^ 65 + 2) * (goldilocksPrime ^ 4 * goldilocksPrime ^ 4)),
      goldilocksPrime ^ 12 - (2 ^ 65 + 2) + 1, Nat.succ_pos _⟩ := by
  decide +kernel

/-! ## The feed-forward term is part of the deployed compression -/

/-- The state with limbs `0, 1, …, 11`. -/
def qipmKatState : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩,
   ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩,
   ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11⟩⟩

/-- The identification of the game's compression with `poseidon2CompressWeighted`, at one
    executed state. -/
theorem qipm_weighted_compress_kat :
    qipmWeightedCompress poseidon2Perm12 qipmKatState = poseidon2CompressWeighted qipmKatState :=
  congrFun qipmWeightedCompress_poseidon2Perm12 qipmKatState

/-- The truncation without feed-forward is a different function: on the same state it does not
    return the digest of `poseidon2CompressWeighted`. -/
theorem tooth_truncation_is_not_poseidon2CompressWeighted :
    ¬ (qipmTruncComp qipmKatState (poseidon2Perm12 qipmKatState) =
      poseidon2CompressWeighted qipmKatState) := by
  decide +kernel

#verify_constructive
  Qsag.qipm_weighted_compress_kat
  Qsag.qipmToyElems_enum
  Qsag.qipm_toy_feed_forward_attack_weight
  Qsag.qipm_toy_feed_forward_bound_applies
  Qsag.qipm_toy_total_weight

#tooth_pair qipm_weighted_compress_kat vs tooth_truncation_is_not_poseidon2CompressWeighted
#tooth_pair qipm_two_way_preimage_bound vs tooth_qipm_no_feedforward_no_capacity_inverted
#tooth_pair qipm_weighted_inverse_fiber vs tooth_qipm_unprotected_fiber_exceeds_lane_square
#tooth_pair qipm_lazy_ideal_perm_capacity4_truncation_collision_128_at_2pow56 vs tooth_poseidon2_unweighted_truncation_not_injective
#tooth_pair qipm_toy_unprotected_attack_certain vs tooth_qipm_toy_feed_forward_defeats_inverse_attack
#tooth_pair qipmPermOracle_swap_agree vs tooth_qipm_swap_changes_marked_point
#tooth_pair qipm_bht_shape_256_up_to_2pow42 vs tooth_qipm_bht_shape_256_fails_at_2pow56
#tooth_pair qipm_grover_shape_256_at_2pow56 vs tooth_qipm_bht_shape_256_fails_at_2pow56
#tooth_pair qipm_lazy_ideal_perm_weighted_feedforward_collision_128_at_2pow56 vs tooth_qipm_collision_bound_shape_fails_at_2pow65

end Qsag
end

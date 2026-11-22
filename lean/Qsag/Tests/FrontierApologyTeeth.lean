module
/-
# Qsag.Tests.FrontierApologyTeeth — falsifiability checks for the frontier reductions

* `Compact1122` (`Qsag.Protocol.Signing.Compact1122ClosedEufCma`):
  - `inhabited_compact1122_honest_signature_verifies`: the forgery experiment is not identically
    lost; the honest signature of every target-sum codeword verifies.
  - `garbageForger_wins_constantHash`: against the constant hash a forger that asks for nothing
    and outputs `34` zero blocks wins on every coin.
  - `tooth_constantHash_forces_trivial_bound`: hence, for the constant hash, the four hardness
    hypotheses of `compact1122_closed_euf_cma_bound` cannot hold with bounds whose combination
    is below `1`, whatever the adversary classes are, as long as they contain the three
    reduction adversaries. One of the reductions wins its experiment.
  - the pair of the bound with the forward-stepping forger for a code without the digit-sum
    constraint.
* `ComputationalMacBlind`: the pairs of the bound with the seed-independent PRG and with the
  unblinded opening, audited across the module boundary.
* `Q192BernoulliTailBound`: the pair of the pointwise error bound with the 8-bit truncation.
-/

public import Qsag.Protocol.Signing.Compact1122ClosedEufCma
public import Qsag.Protocol.Threshold.ComputationalMacBlind
public import Qsag.Math.Q192BernoulliTailBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.FrontierApologyTeeth
open Qsag.Spec Qsag.Compact1122

set_option autoImplicit false

/-! ## `Compact1122` -/

/-- Constant tweakable hash with `32`-byte digests. -/
def constantHash : TwHash := fun _ _ _ => List.replicate 32 0

/-- Injective tweak encoding: slot `n` is `n` zero bytes. -/
def unaryTweak (n : Nat) : Bytes := List.replicate n 0

/-- A target-sum code: `17` digits `95` and `17` digits `0`. -/
def halfCode (_ _ : Bytes) : List Nat := List.replicate 17 95 ++ List.replicate 17 0

theorem constantHash_length (s t m : Bytes) : (constantHash s t m).length = 32 :=
  List.length_replicate

theorem unaryTweak_injective (a b : Nat) (h : unaryTweak a = unaryTweak b) : a = b := by
  have hLen := congrArg List.length h
  unfold unaryTweak at hLen
  rw [List.length_replicate, List.length_replicate] at hLen
  exact hLen

theorem halfCode_ok (r m : Bytes) : CodeOk (halfCode r m) := by
  refine ⟨(by decide : (List.replicate 17 95 ++ List.replicate 17 0).length = 34),
    (by decide : (List.replicate 17 95 ++ List.replicate 17 0).sum = 1615), ?_⟩
  intro a ha
  unfold halfCode at ha
  rcases List.mem_append.mp ha with h | h
  · rw [(List.mem_replicate.mp h).2]; decide
  · rw [(List.mem_replicate.mp h).2]; decide

/-- **The experiment is not identically lost.** For every tweakable hash with `32`-byte digests,
    every coin and every target-sum codeword, the honest signature verifies under the honest
    root. -/
theorem inhabited_compact1122_honest_signature_verifies (th : TwHash) (tw : Nat → Bytes)
    (hOut : ∀ s t m : Bytes, (th s t m).length = 32) {nF : Nat} (ω : Fin (eufCoins nF))
    (c : List Nat) (hc : CodeOk c) :
    verify th tw (seedAt ω)
      (pkRoot th tw (seedAt ω) (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω)))) c
      (signVals (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))) c) = true := by
  refine verify_signVals th tw hOut (seedAt ω) (startsOf (startsIxAt ω))
    (fun i hi => startsOf_length_eq _ i hi) c (fun i hi => ?_)
  have hil : i < c.length := by rw [hc.1]; exact hi
  have hlt : c.getD i 0 < 96 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
    exact hc.2.2 _ (List.getElem_mem _)
  omega

/-- Forger that asks for no signature and outputs `34` zero blocks on the empty message. -/
def garbageForger : Forger where
  query _ _ := none
  forge _ _ _ := ([], [], List.replicate 34 (List.replicate 32 0))

/-- Against the constant hash the garbage forger wins on every coin. -/
theorem garbageForger_wins_constantHash {nF : Nat} (hPos : 0 < eufCoins nF)
    (ω : Fin (eufCoins nF)) :
    (eufGame hPos constantHash unaryTweak halfCode (fun _ _ m => m)
      (fun _ => garbageForger)).win ω = true := by
  rw [eufGame_win_eq]
  have hAll : (List.replicate 34 (List.replicate 32 (0 : UInt8))).all
      (fun v => decide (v.length = 32)) = true := by decide
  show ((match (none : Option (Bytes × List Nat)) with
      | none => true
      | some q => decide (([] : Bytes) ≠ q.1)) &&
    (decide ((List.replicate 34 (List.replicate 32 (0 : UInt8))).length = 34) &&
      ((List.replicate 34 (List.replicate 32 (0 : UInt8))).all (fun v => decide (v.length = 32)) &&
        decide (List.replicate 32 (0 : UInt8) = List.replicate 32 (0 : UInt8))))) = true
  rw [hAll]
  rfl

/-- **Tooth: the hardness hypotheses are load-bearing.** For the constant hash, no assignment
    of bounds to the four hardness hypotheses of `compact1122_closed_euf_cma_bound` combines to
    less than `1`, for any adversary classes containing the reduction adversaries. -/
theorem tooth_constantHash_forces_trivial_bound
    {nF : Nat} (hPos : 0 < eufCoins nF)
    {𝒜I : Code byteOracleIface (Bytes × Bytes) → Prop}
    {𝒜T 𝒜P : Code targetIface TargetBreak → Prop}
    {εItsr εTcr εPre εLink : Spec.RatBound}
    (hAdvI : ∀ b, 𝒜I (itsrAdvAt constantHash unaryTweak halfCode (fun _ _ m => m)
      (fun _ : Fin nF => garbageForger) b))
    (hAdvT : ∀ a, 𝒜T (tcrAdvAt constantHash unaryTweak halfCode (fun _ _ m => m)
      (fun _ : Fin nF => garbageForger) a))
    (hAdvP : ∀ (i : Fin 34) (j : Nat) b, 𝒜P (linkAdvAt constantHash unaryTweak halfCode
      (fun _ _ m => m) (fun _ : Fin nF => garbageForger) i j b))
    (hSmall : ((εItsr.add εTcr).add
      ((Spec.RatBound.scale 34 εPre).add (Spec.RatBound.scale 3196 εLink))).num <
      ((εItsr.add εTcr).add
        ((Spec.RatBound.scale 34 εPre).add (Spec.RatBound.scale 3196 εLink))).den) :
    ¬ (ItsrHard 𝒜I (codeSubset halfCode) 32 1 εItsr ∧
      SmDtTcrHard 𝒜T constantHash 32 3231 εTcr ∧
      SmDtPreHard 𝒜P constantHash 32 32 1 εPre ∧
      ChainLinkHard 𝒜P constantHash unaryTweak εLink) := by
  rintro ⟨hI, hT, hP, hL⟩
  exact FinGame.not_bound_of_forall_win _ (fun ω => garbageForger_wins_constantHash hPos ω) hSmall
    (compact1122_closed_euf_cma_bound unaryTweak unaryTweak_injective
      constantHash_length halfCode halfCode_ok (fun _ _ m => m) (fun _ _ _ _ h => h) hPos
      (fun _ => garbageForger) hI hT hP hL hAdvI hAdvT hAdvP)

/-- **Joint satisfiability.** Every hypothesis of the bound holds for `constantHash`, `unaryTweak`,
    `halfCode`, the identity framing, the unrestricted adversary classes and the trivial bounds
    `1`. The conclusion at this instance carries no information; the instance shows that the
    hypotheses do not contradict one another. -/
theorem compact1122_bound_hypotheses_inhabited {nF : Nat} (hF : 0 < nF) (forger : Fin nF → Forger) :
    GameBound (eufGame (eufCoins_pos hF) constantHash unaryTweak halfCode (fun _ _ m => m) forger).winProb
      ((Spec.RatBound.one.add Spec.RatBound.one).add
        ((Spec.RatBound.scale 34 Spec.RatBound.one).add
          (Spec.RatBound.scale 3196 Spec.RatBound.one))) :=
  compact1122_closed_euf_cma_bound (th := constantHash) unaryTweak unaryTweak_injective
    (fun _ _ _ => List.length_replicate) halfCode halfCode_ok (fun _ _ m => m) (fun _ _ _ _ h => h)
    (eufCoins_pos hF) forger
    (𝒜I := fun _ => True) (𝒜T := fun _ => True) (𝒜P := fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ => FinGame.winProb_le_one _)
    (smDtTcrHard_one _ _ _ _)
    (fun _ _ _ _ _ _ _ _ _ => FinGame.winProb_le_one _)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => FinGame.winProb_le_one _)
    (fun _ => trivial) (fun _ => trivial) (fun _ _ _ => trivial)

#verify_constructive
  Qsag.FrontierApologyTeeth.compact1122_bound_hypotheses_inhabited
  Qsag.FrontierApologyTeeth.inhabited_compact1122_honest_signature_verifies
  Qsag.FrontierApologyTeeth.garbageForger_wins_constantHash
  Qsag.FrontierApologyTeeth.tooth_constantHash_forces_trivial_bound
  Qsag.FrontierApologyTeeth.halfCode_ok
  Qsag.FrontierApologyTeeth.unaryTweak_injective

#tooth_pair Qsag.Compact1122.compact1122_closed_euf_cma_bound vs
  Qsag.Compact1122.tooth_drop_target_sum_forward_step_forges
#tooth_pair Qsag.Compact1122.compact1122_closed_euf_cma_bound vs
  Qsag.FrontierApologyTeeth.tooth_constantHash_forces_trivial_bound

/-! ## `ComputationalMacBlind` -/

#tooth_pair Qsag.MacBlind.computational_macBlind_spdz_security_bound vs
  Qsag.MacBlind.tooth_constant_prg_breaks_blinding
#tooth_pair Qsag.MacBlind.computational_macBlind_tower128_security_bound vs
  Qsag.MacBlind.tooth_constant_prg_breaks_tower128_blinding

/-! ## `Q192BernoulliTailBound` -/

#tooth_pair Qsag.q192_sampler_pointwise_error_le_pow2_neg192 vs
  Qsag.tooth_q8_truncation_violates_2pow_neg128_floor
#tooth_pair Qsag.q192_gaussian_coordinate_tvd_bound vs
  Qsag.tooth_q8_truncation_coordinate_tvd_exceeds_2pow_neg9

end Qsag.FrontierApologyTeeth
end

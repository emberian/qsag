module
public import Qsag.Exec.RssParticipantGateField
import all Qsag.Exec.RssParticipantGateField
import all Qsag.Exec.RssParticipantGateChecks
import all Qsag.Protocol.Threshold.Rss256TernaryRound
import all Qsag.Math.Gf2Pow128
import Qsag.Tactic.AssuranceKit

/-! Multilinear monomial weighting used by `keccak_mpc.rs`, where each binary
word-index bit contributes either one or the corresponding mu/nu challenge.
The coefficient tree is committed before the challenge tuple. These are the
actual degree-one-per-variable weights, not rss256.rs's powers of one chi. -/
public section
namespace Qsag.RssParticipant.GateChecks
open Rss256ProductProof
set_option autoImplicit false
set_option maxRecDepth 8192

abbrev WeightCoeffs := BTree Tower128

def zeroCoeffs : (n : Nat) → WeightCoeffs n
  | 0 => .leaf (towerZero 7)
  | n + 1 => .branch (zeroCoeffs n) (zeroCoeffs n)

def weightEval : {n : Nat} → ChallengeTuple n → WeightCoeffs n → Tower128
  | 0, .nil, .leaf c => c
  | _ + 1, .cons mu rest, .branch lo hi =>
      towerAdd 7 (weightEval rest lo) (towerMul 7 mu (weightEval rest hi))

/-- Number-of-roots bound in the full product coin space. -/
def weightBadBound (cardS : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => weightBadBound cardS n * cardS + cardS ^ n

theorem weightBadBound_scale (cardS n : Nat) :
    weightBadBound cardS n * cardS = n * cardS ^ n := by
  induction n with
  | zero => simp only [weightBadBound, Nat.zero_mul]
  | succ n ih =>
    simp only [weightBadBound, Nat.add_mul]
    rw [ih, Nat.mul_assoc, ← Nat.pow_succ]
    simp only [Nat.one_mul]

private theorem affine_roots_le_one (a b : Tower128)
    (hne : a ≠ towerZero 7 ∨ b ≠ towerZero 7) (S : List Tower128) (hS : S.Nodup) :
    (S.filter (fun x => decide (towerAdd 7 a (towerMul 7 x b) = towerZero 7))).length ≤ 1 := by
  have heq (x : Tower128) : towerAdd 7 a (towerMul 7 x b) =
      RoundPoly.evalCoeffs [a, b] x := by
    change _ = towerAdd 7 a (towerMul 7 x (towerAdd 7 b (towerMul 7 x (towerZero 7))))
    rw [towerMul_zero, towerAdd_zero]
  simp only [heq]
  apply RoundPoly.roots_nodup_length_le 1 [a, b] S hS (Nat.le_refl 2)
  by_cases ha : a = towerZero 7
  · refine ⟨towerOne 7, ?_⟩
    change towerAdd 7 a (towerMul 7 (towerOne 7)
      (towerAdd 7 b (towerMul 7 (towerOne 7) (towerZero 7)))) ≠ towerZero 7
    simp only [ha, towerMul_zero, towerAdd_zero, towerOne_mul, towerZero_add]
    exact hne.resolve_left (fun h => h ha)
  · refine ⟨towerZero 7, ?_⟩
    change towerAdd 7 a (towerMul 7 (towerZero 7) _) ≠ towerZero 7
    simpa only [towerZero_mul, towerAdd_zero] using ha

/-- For any committed nonzero coefficient table, at most n/|S| of independent
uniform n-tuples cancel it. The statement counts finite tuples and makes no
unjustified distribution claim about the cSHAKE weight expansion. -/
theorem weightEval_nonzero_roots_le (S : List Tower128) (hS : S.Nodup) :
    ∀ (n : Nat) (t : WeightCoeffs n), t ≠ zeroCoeffs n →
      ((challengeTuples S n).filter (fun gs => decide (weightEval gs t = towerZero 7))).length ≤
        weightBadBound S.length n := by
  intro n
  induction n with
  | zero =>
    intro t ht
    cases t with | leaf c =>
    have hc : c ≠ towerZero 7 := fun h => ht (by rw [h]; rfl)
    have hf : decide (weightEval ChallengeTuple.nil (.leaf c) = towerZero 7) = false :=
      decide_eq_false_iff_not.mpr hc
    unfold challengeTuples List.filter weightBadBound
    rw [hf]
    exact Nat.le_refl 0
  | succ n ih =>
    intro t ht
    cases t with | branch lo hi =>
    have hpick : ∃ chosen : WeightCoeffs n, chosen ≠ zeroCoeffs n ∧
        ∀ rest : ChallengeTuple n, weightEval rest chosen ≠ towerZero 7 →
          weightEval rest lo ≠ towerZero 7 ∨ weightEval rest hi ≠ towerZero 7 := by
      by_cases hlo : lo = zeroCoeffs n
      · exact ⟨hi, fun hhi => ht (by rw [hlo, hhi]; rfl), fun _ h => Or.inr h⟩
      · exact ⟨lo, hlo, fun _ h => Or.inl h⟩
    rcases hpick with ⟨chosen, hchosen, himp⟩
    unfold challengeTuples weightBadBound
    rw [filter_flatMap_len]
    have hsplit := sum_map_le_split
      (fun rest => decide (weightEval rest chosen = towerZero 7))
      (fun rest => ((S.map (fun g => ChallengeTuple.cons g rest)).filter
        (fun gs => decide (weightEval gs (.branch lo hi) = towerZero 7))).length)
      S.length 1
      (fun rest _ => by
        rw [filter_map_len]
        exact List.length_filter_le _ S)
      (fun rest hgood => by
        rw [filter_map_len]
        exact affine_roots_le_one _ _ (himp rest (decide_eq_false_iff_not.mp hgood)) S hS)
      (challengeTuples S n)
    rw [challengeTuples_length, Nat.mul_one] at hsplit
    exact Nat.le_trans hsplit
      (Nat.add_le_add_right (Nat.mul_le_mul_right S.length (ih chosen hchosen)) _)

/-- Aligned records after replica consistency and transcript indexing. This
shape does not itself assert consistency with delivered network envelopes. -/
abbrev GateTable (n : Nat) := BTree (GateRecord × GateRecord × GateRecord) n

def gateCoeffs : {n : Nat} → GateTable n → WeightCoeffs n
  | 0, .leaf (a, b, c) => .leaf (gateError a b c)
  | _ + 1, .branch lo hi => .branch (gateCoeffs lo) (gateCoeffs hi)

def gateTableValid : {n : Nat} → GateTable n → Prop
  | 0, .leaf (a, b, c) => relation a b c
  | _ + 1, .branch lo hi => gateTableValid lo ∧ gateTableValid hi

theorem gateCoeffs_zero_iff : ∀ (n : Nat) (t : GateTable n),
    gateCoeffs t = zeroCoeffs n ↔ gateTableValid t := by
  intro n
  induction n with
  | zero =>
    intro t
    cases t with | leaf triple =>
    rcases triple with ⟨a, b, c⟩
    simp only [gateCoeffs, zeroCoeffs, gateTableValid, BTree.leaf.injEq]
    exact gateError_zero_iff a b c
  | succ n ih =>
    intro t
    cases t with | branch lo hi =>
    simp only [gateCoeffs, zeroCoeffs, gateTableValid, BTree.branch.injEq, ih]

def claimedCoeffs : {n : Nat} → GateTable n → WeightCoeffs n
  | 0, .leaf (a, b, c) => .leaf (wordToField (a.product ^^^ b.product ^^^ c.product))
  | _ + 1, .branch lo hi => .branch (claimedCoeffs lo) (claimedCoeffs hi)

def trueCoeffs : {n : Nat} → GateTable n → WeightCoeffs n
  | 0, .leaf (a, b, c) => .leaf (wordToField
      ((a.lhsOwn ^^^ b.lhsOwn ^^^ c.lhsOwn) &&& (a.rhsOwn ^^^ b.rhsOwn ^^^ c.rhsOwn)))
  | _ + 1, .branch lo hi => .branch (trueCoeffs lo) (trueCoeffs hi)

/-- The error polynomial is exactly weighted c minus weighted Boolean a AND b.
This supplies the initial-claim defect identity, before tensor compression. -/
theorem weighted_claim_defect : ∀ (n : Nat) (t : GateTable n) (gs : ChallengeTuple n),
    weightEval gs (gateCoeffs t) =
      towerAdd 7 (weightEval gs (claimedCoeffs t)) (weightEval gs (trueCoeffs t)) := by
  intro n
  induction n with
  | zero =>
    intro t gs
    cases t with | leaf triple =>
    cases gs
    rcases triple with ⟨a, b, c⟩
    exact wordToField_xor _ _
  | succ n ih =>
    intro t gs
    cases t with | branch lo hi =>
    cases gs with | cons mu rest =>
    simp only [gateCoeffs, claimedCoeffs, trueCoeffs, weightEval, ih,
      towerMul_add_distrib]
    ac_rfl

/-- Actual committed AND error coefficients, with nonzero embedding proved:
invalid gates can cancel initial monomial weighting only on this counted event. -/
theorem invalid_gate_weight_cancellation_le (n : Nat) (t : GateTable n)
    (hinvalid : ¬ gateTableValid t) (S : List Tower128) (hS : S.Nodup) :
    ((challengeTuples S n).filter (fun gs =>
      decide (weightEval gs (gateCoeffs t) = towerZero 7))).length ≤
        weightBadBound S.length n := by
  exact weightEval_nonzero_roots_le S hS n (gateCoeffs t)
    (fun h => hinvalid ((gateCoeffs_zero_iff n t).mp h))

/-- Malicious initial claim equality, expressed through actual committed
product-word shares rather than an unconstrained error-polynomial oracle. -/
theorem invalid_weighted_claim_equal_le (n : Nat) (t : GateTable n)
    (hinvalid : ¬ gateTableValid t) (S : List Tower128) (hS : S.Nodup) :
    ((challengeTuples S n).filter (fun gs => decide
      (weightEval gs (claimedCoeffs t) = weightEval gs (trueCoeffs t)))).length ≤
        weightBadBound S.length n := by
  apply Nat.le_trans (filter_len_le_of_imp _
    (fun gs => decide (weightEval gs (gateCoeffs t) = towerZero 7)) ?_ (challengeTuples S n))
  · exact invalid_gate_weight_cancellation_le n t hinvalid S hS
  · intro gs h
    apply decide_eq_true_iff.mpr
    rw [weighted_claim_defect, decide_eq_true_iff.mp h, towerAdd_self_zero]

#verify_constructive weightBadBound_scale weightEval_nonzero_roots_le
  gateCoeffs_zero_iff invalid_gate_weight_cancellation_le
  weighted_claim_defect invalid_weighted_claim_equal_le
end Qsag.RssParticipant.GateChecks
end

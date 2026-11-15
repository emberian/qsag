module
public import Qsag.RssParticipantMachine
public import Qsag.Rss256TernaryRound
import all Qsag.RssParticipantMachine
import all Qsag.RssParticipantKeccak
import all Qsag.ThresholdMpc
import all Qsag.Rss256TernaryRound
import all Qsag.BinaryTower
import Qsag.Tactic.AssuranceKit

/-!
The actual `keccak_mpc.rs` final product check is a SINGLE masked product, not
rss256.rs's cross product. This module proves that check directly. The imported
ternary module supplies field polynomial root counting only. It does not import
or apply the separate rss256 two-pass security theorem.

`FinalCommitment` contains all coefficients fixed BEFORE tau. A strategy may
choose it from the entire preceding history, but not from the future tau.
No cut capability is minted here: the packed six-round tensor reduction and
its connection to retained participant round evidence are still needed.
-/
public section
namespace Qsag.RssParticipant.GateChecks
open Rss256ProductProof
set_option autoImplicit false
set_option maxRecDepth 8192

/-- Reconstructed Boolean relation belonging to three aligned local records. -/
def relation (g0 g1 g2 : GateRecord) : Prop :=
  (g0.product ^^^ g1.product ^^^ g2.product) =
    ((g0.lhsOwn ^^^ g1.lhsOwn ^^^ g2.lhsOwn) &&&
      (g0.rhsOwn ^^^ g1.rhsOwn ^^^ g2.rhsOwn))

instance (g0 g1 g2 : GateRecord) : Decidable (relation g0 g1 g2) :=
by
  exact inferInstanceAs (Decidable ((g0.product ^^^ g1.product ^^^ g2.product) =
    ((g0.lhsOwn ^^^ g1.lhsOwn ^^^ g2.lhsOwn) &&&
      (g0.rhsOwn ^^^ g1.rhsOwn ^^^ g2.rhsOwn))))

theorem honest_relation (a b : RssWord64) (r : RssPrfZeroSeeds) :
    relation (productGate a.x0 a.x1 b.x0 b.x1 (r.r0, r.r1))
      (productGate a.x1 a.x2 b.x1 b.x2 (r.r1, r.r2))
      (productGate a.x2 a.x0 b.x2 b.x0 (r.r2, r.r0)) := by
  exact reconstructRssWord_rssWordAnd a b r

/-- A tampered product is not hidden by the local record type. -/
theorem tampered_zero_gate_rejected :
    ¬ relation ⟨0, 0, 0, 0, 1⟩ ⟨0, 0, 0, 0, 0⟩ ⟨0, 0, 0, 0, 0⟩ := by
  decide

/-- Reconstructed values AFTER verified replicated-share commit/open.
The low-level commitment binding and replica comparison precede this layer. -/
structure FinalCommitment where
  x : Tower128
  y : Tower128
  claim : Tower128
  rx : Tower128
  ry : Tower128
  c0 : Tower128
  c1 : Tower128

/-- `rss_dzk_pass`: `rx + tau*x`, `ry + tau*y`, `c0 + tau*c1 + tau²*claim`. -/
def finalOpening (c : FinalCommitment) (tau : Tower128) : Tower128 × Tower128 × Tower128 :=
  (towerAdd 7 c.rx (towerMul 7 tau c.x),
   towerAdd 7 c.ry (towerMul 7 tau c.y),
   towerAdd 7 (towerAdd 7 c.c0 (towerMul 7 tau c.c1))
     (towerMul 7 (towerMul 7 tau tau) c.claim))

def accepts (c : FinalCommitment) (tau : Tower128) : Bool :=
  let o := finalOpening c tau
  decide (towerMul 7 o.1 o.2.1 = o.2.2)

def residual (c : FinalCommitment) : List Tower128 :=
  [towerAdd 7 (towerMul 7 c.rx c.ry) c.c0,
   towerAdd 7 (towerAdd 7 (towerMul 7 c.rx c.y) (towerMul 7 c.x c.ry)) c.c1,
   towerAdd 7 (towerMul 7 c.x c.y) c.claim]

private theorem add_zero_iff (a b : Tower128) :
    towerAdd 7 a b = towerZero 7 ↔ a = b := by
  constructor
  · intro h
    have hh := congrArg (fun z => towerAdd 7 z b) h
    rw [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] at hh
    exact hh
  · rintro rfl
    exact towerAdd_self_zero 7 a

/-- The checker error is an explicit polynomial of degree at most two. -/
theorem accepts_iff_residual_zero (c : FinalCommitment) (tau : Tower128) :
    accepts c tau = true ↔ RoundPoly.evalCoeffs (residual c) tau = towerZero 7 := by
  change decide (_ = _) = true ↔ _
  rw [decide_eq_true_eq, ← add_zero_iff]
  have heq :
      towerAdd 7 (towerMul 7 (finalOpening c tau).1 (finalOpening c tau).2.1)
        (finalOpening c tau).2.2 = RoundPoly.evalCoeffs (residual c) tau := by
    simp only [finalOpening, residual, evalCoeffs3_eq, towerAdd_mul_distrib,
      towerMul_add_distrib]
    rw [show towerMul 7 c.rx (towerMul 7 tau c.y) =
          towerMul 7 tau (towerMul 7 c.rx c.y) by ac_rfl,
        show towerMul 7 (towerMul 7 tau c.x) c.ry =
          towerMul 7 tau (towerMul 7 c.x c.ry) by ac_rfl,
        show towerMul 7 (towerMul 7 tau c.x) (towerMul 7 tau c.y) =
          towerMul 7 tau (towerMul 7 tau (towerMul 7 c.x c.y)) by ac_rfl,
        show towerMul 7 (towerMul 7 tau tau) c.claim =
          towerMul 7 tau (towerMul 7 tau c.claim) by ac_rfl]
    ac_rfl
  rw [heq]

theorem honest_final_complete (c : FinalCommitment)
    (h0 : c.c0 = towerMul 7 c.rx c.ry)
    (h1 : c.c1 = towerAdd 7 (towerMul 7 c.rx c.y) (towerMul 7 c.x c.ry))
    (h2 : c.claim = towerMul 7 c.x c.y) (tau : Tower128) :
    accepts c tau = true := by
  rw [accepts_iff_residual_zero]
  simp only [residual, h0, h1, h2, towerAdd_self_zero, evalCoeffs3_eq,
    towerMul_zero]

/-- Explicit bad-challenge event. Coefficients may be malicious but must be fixed.
The final coefficient is nonzero exactly when the remaining product claim is false. -/
def badChallenge (c : FinalCommitment) (tau : Tower128) : Bool :=
  decide (c.claim ≠ towerMul 7 c.x c.y) && accepts c tau

theorem accepted_correct_or_bad (c : FinalCommitment) (tau : Tower128)
    (h : accepts c tau = true) :
    c.claim = towerMul 7 c.x c.y ∨ badChallenge c tau = true := by
  by_cases hc : c.claim = towerMul 7 c.x c.y
  · exact Or.inl hc
  · exact Or.inr (by simp [badChallenge, hc, h])

/-- Finite counting, hence probability ≤2/|S| for a fresh uniform tau in S.
There is no uniformity claim about cSHAKE-expanded coins in this theorem. -/
theorem false_final_accepting_challenges_le_two (c : FinalCommitment)
    (hfalse : c.claim ≠ towerMul 7 c.x c.y) (S : List Tower128) (hS : S.Nodup) :
    (S.filter (accepts c)).length ≤ 2 := by
  have hn : towerAdd 7 (towerMul 7 c.x c.y) c.claim ≠ towerZero 7 := by
    intro hz
    exact hfalse ((add_zero_iff _ _).mp hz).symm
  have hp : accepts c = fun tau => decide (RoundPoly.evalCoeffs (residual c) tau = towerZero 7) := by
    funext tau
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact accepts_iff_residual_zero c tau
  rw [hp]
  exact quadratic_roots_le_two_tower128 _ _ _ S hS (Or.inr (Or.inr hn))

/-- Choosing c0 AFTER tau defeats the check at every challenge. This negative
control makes the pre-challenge commitment order essential, not documentation. -/
def lateForgery (tau : Tower128) : FinalCommitment :=
  ⟨towerZero 7, towerZero 7, towerOne 7, towerZero 7, towerZero 7,
    towerMul 7 tau tau, towerZero 7⟩

theorem late_commitment_forges (tau : Tower128) :
    (lateForgery tau).claim ≠ towerMul 7 (lateForgery tau).x (lateForgery tau).y ∧
      accepts (lateForgery tau) tau = true := by
  constructor
  · simp only [lateForgery, towerMul_zero]
    decide
  · simp only [accepts, finalOpening, lateForgery, towerMul_zero, towerAdd_zero,
      towerMul_one, towerAdd_self_zero, decide_true]

/-- Error propagation in Rust's inverse-challenge halving round. `delta` is
claim minus the true dot product; eL/eR are the fixed cross-term message errors. -/
def foldError (delta eL eR gamma : Tower128) : Tower128 :=
  towerAdd 7 (towerAdd 7 delta (towerMul 7 (towerInv 7 gamma) eL))
    (towerMul 7 gamma eR)

def foldBad (delta eL eR gamma : Tower128) : Bool :=
  decide (gamma ≠ towerZero 7) && decide (foldError delta eL eR gamma = towerZero 7)

/-- Pointwise vector-fold identity. Summing it gives the dot-product update;
zero-padding absent upper-half elements is respected because it holds at zero. -/
theorem fold_product_expand (xlo xhi ylo yhi gamma : Tower128)
    (hg : gamma ≠ towerZero 7) :
    towerMul 7 (towerAdd 7 xlo (towerMul 7 gamma xhi))
      (towerAdd 7 ylo (towerMul 7 (towerInv 7 gamma) yhi)) =
    towerAdd 7 (towerAdd 7
      (towerAdd 7 (towerMul 7 xlo ylo) (towerMul 7 xhi yhi))
      (towerMul 7 (towerInv 7 gamma) (towerMul 7 xlo yhi)))
      (towerMul 7 gamma (towerMul 7 xhi ylo)) := by
  simp only [towerMul_add_distrib, towerAdd_mul_distrib]
  rw [show towerMul 7 (towerMul 7 gamma xhi) (towerMul 7 (towerInv 7 gamma) yhi) =
      towerMul 7 (towerMul 7 gamma (towerInv 7 gamma)) (towerMul 7 xhi yhi) by ac_rfl,
    towerMul_inv 7 gamma hg, towerOne_mul]
  ac_rfl

theorem foldError_scaled (delta eL eR gamma : Tower128)
    (hg : gamma ≠ towerZero 7) :
    towerMul 7 gamma (foldError delta eL eR gamma) =
      RoundPoly.evalCoeffs [eL, delta, eR] gamma := by
  simp only [foldError, towerMul_add_distrib, evalCoeffs3_eq]
  rw [← towerMul_assoc 7 gamma (towerInv 7 gamma), towerMul_inv 7 gamma hg,
    towerOne_mul]
  ac_rfl

theorem false_fold_bad_challenges_le_two (delta eL eR : Tower128)
    (hd : delta ≠ towerZero 7) (S : List Tower128) (hS : S.Nodup) :
    (S.filter (foldBad delta eL eR)).length ≤ 2 := by
  apply Nat.le_trans (filter_len_le_of_imp (foldBad delta eL eR)
    (fun gamma => decide (RoundPoly.evalCoeffs [eL, delta, eR] gamma = towerZero 7)) ?_ S)
  · exact quadratic_roots_le_two_tower128 eL delta eR S hS (Or.inr (Or.inl hd))
  · intro gamma h
    simp only [foldBad, Bool.and_eq_true, decide_eq_true_eq] at h
    apply decide_eq_true_iff.mpr
    rw [← foldError_scaled delta eL eR gamma h.1, h.2, towerMul_zero]

/-- The zero challenge is excluded even if the residual would vanish there. -/
theorem fold_zero_rejected (delta eL eR : Tower128) :
    foldBad delta eL eR (towerZero 7) = false := by
  simp [foldBad]

/-- Packed-round weight `1 + gamma * (1 + mu)` from `rss_dzk_pass`. -/
def packedWeight (mu gamma : Tower128) : Tower128 :=
  towerAdd 7 (towerOne 7) (towerMul 7 gamma (towerAdd 7 (towerOne 7) mu))

/-- Difference between the locked prover quadratic and the true quadratic.
At Boolean endpoints its weighted sum is exactly the incoming claim error. -/
def packedResidual (delta mu e1 e2 : Tower128) : List Tower128 :=
  let e0 := towerAdd 7 delta (towerMul 7 mu e1)
  [e0, towerAdd 7 (towerAdd 7 e0 e1) e2, e2]

def packedBad (delta mu e1 e2 gamma : Tower128) : Bool :=
  decide (towerMul 7 (packedWeight mu gamma)
    (RoundPoly.evalCoeffs (packedResidual delta mu e1 e2) gamma) = towerZero 7)

/-- Exact scalar update of `rss_dzk_pass`, with `s0` locked from the claim. -/
def packedNext (claim mu s1 s2 gamma : Tower128) : Tower128 :=
  let w := packedWeight mu gamma
  let c0 := towerMul 7 w (towerAdd 7 (towerOne 7) gamma)
  let c1 := towerMul 7 w gamma
  let c2 := towerMul 7 w (towerAdd 7 gamma (towerMul 7 gamma gamma))
  towerAdd 7 (towerAdd 7 (towerMul 7 c0 (towerAdd 7 claim (towerMul 7 mu s1)))
    (towerMul 7 c1 s1)) (towerMul 7 c2 s2)

theorem packedNext_honest (s0 mu s1 s2 gamma : Tower128) :
    packedNext (towerAdd 7 s0 (towerMul 7 mu s1)) mu s1 s2 gamma =
      towerMul 7 (packedWeight mu gamma)
        (towerAdd 7 (towerAdd 7
          (towerMul 7 (towerAdd 7 (towerOne 7) gamma) s0)
          (towerMul 7 gamma s1))
          (towerMul 7 (towerAdd 7 gamma (towerMul 7 gamma gamma)) s2)) := by
  simp only [packedNext, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero,
    towerMul_add_distrib, towerAdd_mul_distrib, towerMul_one, towerOne_mul, towerMul_assoc]

theorem packedNext_error (claim honestClaim mu s1 honestS1 s2 honestS2 gamma : Tower128) :
    towerAdd 7 (packedNext claim mu s1 s2 gamma)
      (packedNext honestClaim mu honestS1 honestS2 gamma) =
    packedNext (towerAdd 7 claim honestClaim) mu (towerAdd 7 s1 honestS1)
      (towerAdd 7 s2 honestS2) gamma := by
  simp only [packedNext, towerMul_add_distrib]
  ac_rfl

theorem packedNext_eq_residual (delta mu e1 e2 gamma : Tower128) :
    packedNext delta mu e1 e2 gamma = towerMul 7 (packedWeight mu gamma)
      (RoundPoly.evalCoeffs (packedResidual delta mu e1 e2) gamma) := by
  simp only [packedNext, packedResidual, evalCoeffs3_eq, towerMul_add_distrib,
    towerAdd_mul_distrib, towerMul_one]
  simp only [towerMul_assoc]
  ac_rfl

private theorem filter_or_le {A : Type} (p q : A → Bool) (S : List A) :
    (S.filter (fun a => p a || q a)).length ≤ (S.filter p).length + (S.filter q).length := by
  induction S with
  | nil => exact Nat.le_refl 0
  | cons a S ih =>
    simp only [List.filter_cons]
    cases p a <;> cases q a <;> simp_all <;> omega

private theorem packed_weight_roots_le_one (mu : Tower128) (S : List Tower128) (hS : S.Nodup) :
    (S.filter (fun g => decide (packedWeight mu g = towerZero 7))).length ≤ 1 := by
  have heq (g : Tower128) : packedWeight mu g =
      RoundPoly.evalCoeffs [towerOne 7, towerAdd 7 (towerOne 7) mu] g := by
    change _ = towerAdd 7 (towerOne 7) (towerMul 7 g
      (towerAdd 7 (towerAdd 7 (towerOne 7) mu) (towerMul 7 g (towerZero 7))))
    rw [towerMul_zero, towerAdd_zero]
    rfl
  simp only [heq]
  apply RoundPoly.roots_nodup_length_le 1
    [towerOne 7, towerAdd 7 (towerOne 7) mu] S hS (Nat.le_refl 2)
  refine ⟨towerZero 7, ?_⟩
  change towerAdd 7 (towerOne 7) (towerMul 7 (towerZero 7) _) ≠ towerZero 7
  rw [towerZero_mul, towerAdd_zero]
  decide

/-- Six applications cost at most 18/|S|: each bad event is the union of one
linear-weight root and at most two quadratic-error roots. No generic
'accepted implies valid' condition is used to obtain this local bound. -/
theorem false_packed_bad_challenges_le_three (delta mu e1 e2 : Tower128)
    (hd : delta ≠ towerZero 7) (S : List Tower128) (hS : S.Nodup) :
    (S.filter (packedBad delta mu e1 e2)).length ≤ 3 := by
  let e0 := towerAdd 7 delta (towerMul 7 mu e1)
  have hn : e0 ≠ towerZero 7 ∨ towerAdd 7 (towerAdd 7 e0 e1) e2 ≠ towerZero 7 ∨
      e2 ≠ towerZero 7 := by
    by_cases h0 : e0 = towerZero 7
    · by_cases h2 : e2 = towerZero 7
      · right; left
        simp only [h0, h2, towerZero_add, towerAdd_zero]
        intro h1
        have hh : delta = towerZero 7 := by
          simpa only [e0, h1, towerMul_zero, towerAdd_zero] using h0
        exact hd hh
      · exact Or.inr (Or.inr h2)
    · exact Or.inl h0
  have hquad := quadratic_roots_le_two_tower128 e0
    (towerAdd 7 (towerAdd 7 e0 e1) e2) e2 S hS hn
  have heq : packedBad delta mu e1 e2 = fun g =>
      decide (packedWeight mu g = towerZero 7) ||
      decide (RoundPoly.evalCoeffs (packedResidual delta mu e1 e2) g = towerZero 7) := by
    funext g
    apply Bool.eq_iff_iff.mpr
    simp only [packedBad, decide_eq_true_eq, Bool.or_eq_true, towerMul_eq_zero_iff]
  rw [heq]
  have hu := filter_or_le (fun g => decide (packedWeight mu g = towerZero 7))
    (fun g => decide (RoundPoly.evalCoeffs (packedResidual delta mu e1 e2) g = towerZero 7)) S
  exact Nat.le_trans hu (Nat.add_le_add (packed_weight_roots_le_one mu S hS) hquad)

/-- Malicious packed message values enter the actual update. No premise that
prover messages are correct occurs in this counting theorem. -/
theorem packed_false_claim_repair_challenges_le_three
    (claim honestClaim mu s1 honestS1 s2 honestS2 : Tower128)
    (hf : claim ≠ honestClaim) (S : List Tower128) (hS : S.Nodup) :
    (S.filter (fun gamma => decide (packedNext claim mu s1 s2 gamma =
      packedNext honestClaim mu honestS1 honestS2 gamma))).length ≤ 3 := by
  have hd : towerAdd 7 claim honestClaim ≠ towerZero 7 := by
    intro h
    exact hf ((add_zero_iff _ _).mp h)
  have hp : (fun gamma => decide (packedNext claim mu s1 s2 gamma =
      packedNext honestClaim mu honestS1 honestS2 gamma)) =
      packedBad (towerAdd 7 claim honestClaim) mu (towerAdd 7 s1 honestS1)
        (towerAdd 7 s2 honestS2) := by
    funext gamma
    apply decide_eq_decide_of_iff
    rw [← add_zero_iff, packedNext_error, packedNext_eq_residual]
  rw [hp]
  exact false_packed_bad_challenges_le_three _ _ _ _ hd S hS

#verify_constructive honest_relation tampered_zero_gate_rejected
  accepts_iff_residual_zero honest_final_complete accepted_correct_or_bad
  false_final_accepting_challenges_le_two late_commitment_forges
  foldError_scaled false_fold_bad_challenges_le_two fold_zero_rejected
  false_packed_bad_challenges_le_three packedNext_error packedNext_eq_residual
  packedNext_honest fold_product_expand packed_false_claim_repair_challenges_le_three
end Qsag.RssParticipant.GateChecks
end

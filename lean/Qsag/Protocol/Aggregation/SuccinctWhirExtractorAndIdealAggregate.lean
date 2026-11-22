module
/-
# Qsag.Protocol.Aggregation.SuccinctWhirExtractorAndIdealAggregate — Succinct Fiat–Shamir QROM WHIR Knowledge Extraction & `Spec.IdealAggregate` Refinement (`< 2^{-128}`)

Closes the succinct single-layer knowledge-extraction and `Spec.IdealAggregate` refinement gap
(`ASSURANCE.md:124`):
1. **Unconditional Quintic `WhirScheduleCert` (`zkHemV2Uncond128Cert`):**
   Constructs an unconditional 102-query `WhirScheduleCert` on `QuinticGoldilocks` (`𝔽_{p^5}`) over
   `quinticCoset64` (`9^{102} / 64^{102} < 2^{-288}`), proving both single-proof and `(2^{17} - 1)`-node
   (`< 2^{-128}` at `Q ≤ 2^{64}`) QROM soundness across `.turboShake400` and `.poseidon2Gl24`.
2. **Succinct Fiat–Shamir QROM WHIR Verifier (`SuccinctWhirAggregateProof`, `verifySuccinctWhirAggregate`):**
   Transmits zero `StepOpRow`s and zero `AggNativeSignature`s (`succinctWhirProofSigs = fun _ => []`);
   verifies ONLY salted Merkle-Canopy roots, Fiat–Shamir challenges, `5` OOD evaluation pins, folded
   sumcheck rounds, and `102` Canopy Merkle openings via `ClosedFs.succinctVerify`.
3. **Straight-Line QROM Query-Table Extractor (`whirTableBackedMessages`, `extractSuccinctWhirAggregate`):**
   Reconstructs committed WHIR tables and salted Stage-0 `StepOp256` slot row blocks directly from the
   prover's recorded oracle transcript `log` (`extractOnlineMerkleOpening`) with zero rewinding, proving
   `Spec.StraightLineExtractor (decodeSlotLeafSig slotC) (fun _ => [])` and extracting valid native
   signatures for BOTH `.xmssPoseidon2` (`stepOp256TableOk_xmss_extract`) and `.corduroyPoseidon2`
   (`stepOp256TableOk_corduroy_extract`).
4. **Landmark Soundness & `Spec.IdealAggregate` Refinement (`< 2^{-128}` at `Q ≤ 2^{64}`):**
   - `succinctWhirAggregate_extractorSound`: instantiates `Spec.AggregateExtractorSound` over
     `Spec.StraightLineExtractor (decodeSlotLeafSig slotC) (fun _ => [])` strictly `< 2^{-128}`.
   - `succinctWhirAggregate_refines_idealAggregate_128`: proves `Spec.DataRefines` forward simulation
     into `Spec.idealAggregateMachine` paired with `< 2^{-128}` extraction-failure bound at `Q ≤ 2^{64}`.
-/

public import Qsag.Spec.IdealAggregate
public import Qsag.Spec.GameBound
public import Qsag.Spec.Refines
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Protocol.Aggregation.ClosedWhirSchedule
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness
public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
public import Qsag.Protocol.Aggregation.ZkHemV2ScheduleCert
public import Qsag.Protocol.Aggregation.ZkHemV2PackedFiberCerts
import Qsag.Tactic.AssuranceKit

public section
attribute [-instance] Fin.instLinearOrderPackage

namespace Qsag.SuccinctWhirAgg

open Qsag Qsag.ClosedFs Qsag.ClosedWhir Qsag.ZkHemV2Cert Qsag.ZkHemV2Packed

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 100000

local infixl:65 " +ᵍ " => CommRingOps.add
local infixl:65 " -ᵍ " => CommRingOps.sub
local infixl:70 " *ᵍ " => CommRingOps.mul

/-! ## §1. Unconditional 102-Query `WhirScheduleCert` on `QuinticGoldilocks` (`< 2^{-128}` at `Q ≤ 2^{64}`) -/

/-- Unconditional 102-query Stage-0 WHIR specification on `quinticCoset64` (`9^{102} / 64^{102} < 2^{-288}`). -/
@[expose] def zkHemV2Uncond128Stage : WhirStage :=
  ⟨0, 6, 6, 5, 102, 1, 9, 1, 65, 260, 1, 0⟩

@[expose] def zkHemV2Uncond128Sched : WhirVerifierSchedule :=
  ⟨6, quinticGoldilocksCard, quinticGoldilocksCard_pos, [zkHemV2Uncond128Stage]⟩

theorem zkHemV2Uncond128Sched_johnsonOk : zkHemV2Uncond128Sched.johnsonOk = true := by
  decide +kernel

@[expose] def zkHemV2Uncond128Env : WhirEnv QuinticGoldilocks where
  chalField := fun c j => QuinticGoldilocks.ofBase (Goldilocks.ofNat ((c / 64 ^ j) % 64))
  chalPos := fun c j _ => (c / 64 ^ j) % 64
  domPt := fun _ p => quinticCoset64.getD p CommRingOps.zero
  fold2 := fun _ _ a _ => a
  finalClaim := fun p _ => RoundPoly.evalCoeffs p CommRingOps.zero
  initClaim := fun p => RoundPoly.evalCoeffs p CommRingOps.zero
  finalDeg := 1

private def allGood64U (good : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | t + 1, u => good (u % 64) && allGood64U good t (u / 64)

private theorem allGood64U_of_range (good : Nat → Bool) :
    ∀ (t u : Nat), (∀ j < t, good ((u / 64 ^ j) % 64) = true) → allGood64U good t u = true
  | 0, _, _ => rfl
  | t + 1, u, h => by
    unfold allGood64U
    have h0 := h 0 (Nat.zero_lt_succ t)
    rw [Nat.pow_zero, Nat.div_one] at h0
    have ih := allGood64U_of_range good t (u / 64) (fun j hj => by
      have hj1 := h (j + 1) (Nat.succ_lt_succ hj)
      rwa [Nat.pow_succ', ← Nat.div_div_eq_div_mul] at hj1)
    rw [h0, ih]; rfl

private theorem qsum_mul_div_mod_u (a b : Nat) (hb : 0 < b) (g : Nat → Nat → Nat) :
    qsum (a * b) (fun i => g (i.1 / b) (i.1 % b)) =
      qsum a (fun q => qsum b (fun r => g q.1 r.1)) := by
  induction a with
  | zero => rw [Nat.zero_mul, qsum_zero, qsum_zero]
  | succ a ih =>
    have hSplit := qsum_split_add_p (a * b) (fun u => g (u / b) (u % b)) b
    rw [Nat.succ_mul, hSplit, ih, qsum_append_one a (fun k => qsum b (fun r => g k r.1))]
    refine congrArg (qsum a _ + ·) ?_
    exact qsum_congr (fun r => by
      have hDiv : (a * b + r.1) / b = a := by
        rw [Nat.mul_comm a b, Nat.mul_add_div hb, Nat.div_eq_of_lt r.2, Nat.add_zero]
      have hMod : (a * b + r.1) % b = r.1 := by
        rw [Nat.mul_comm a b, Nat.mul_add_mod, Nat.mod_eq_of_lt r.2]
      rw [hDiv, hMod])

private theorem qsum_allGood64U_le (B : Nat) (good : Nat → Bool)
    (hGood : qsum 64 (fun i => if good i.1 = true then 1 else 0) ≤ B) :
    ∀ t : Nat, qsum (64 ^ t) (fun u => if allGood64U good t u.1 = true then 1 else 0) ≤ B ^ t
  | 0 => by show qsum 1 _ ≤ 1; rw [qsum_succ, qsum_zero]; exact Nat.le_refl 1
  | t + 1 => by
    have hPow : 64 ^ (t + 1) = 64 ^ t * 64 := Nat.pow_succ 64 t
    have hCongr : ∀ (m n : Nat), m = n → ∀ (f : Nat → Nat),
        qsum m (fun i => f i.1) = qsum n (fun j => f j.1) := by intro m n hm _; subst hm; rfl
    rw [hCongr _ _ hPow (fun u => if allGood64U good (t + 1) u = true then 1 else 0)]
    have hRew : ∀ c : Fin (64 ^ t * 64),
        (if allGood64U good (t + 1) c.1 = true then 1 else 0) =
        (if allGood64U good t (c.1 / 64) = true then 1 else 0) *
          (if good (c.1 % 64) = true then 1 else 0) := by
      intro c
      have hAnd : ∀ (u v : Bool),
          (if (u && v) = true then 1 else 0) =
          (if v = true then 1 else 0) * (if u = true then 1 else 0) := by
        intro u v; cases u <;> cases v <;> rfl
      exact hAnd (good (c.1 % 64)) (allGood64U good t (c.1 / 64))
    rw [qsum_congr hRew, qsum_mul_div_mod_u (64 ^ t) 64 (by decide)
      (fun q r => (if allGood64U good t q = true then 1 else 0) * (if good r = true then 1 else 0))]
    have hFactor : ∀ i : Fin (64 ^ t),
        qsum 64 (fun j => (if allGood64U good t i.1 = true then 1 else 0) *
          (if good j.1 = true then 1 else 0)) ≤
        (if allGood64U good t i.1 = true then 1 else 0) * B := by
      intro i; cases allGood64U good t i.1
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul]; rw [qsum_const, Nat.mul_zero]; exact Nat.le_refl 0
      · simp only [↓reduceIte, Nat.one_mul]; exact hGood
    have hStep1 := qsum_le_qsum hFactor
    have hScale : ∀ (m c : Nat) (f : Fin m → Nat), qsum m (fun i => f i * c) = qsum m f * c := by
      intro m c f; induction m with
      | zero => rw [qsum_zero, qsum_zero, Nat.zero_mul]
      | succ m ihm => rw [qsum_succ, qsum_succ, Nat.add_mul, ihm]
    rw [hScale] at hStep1
    rw [Nat.pow_succ]
    exact Nat.le_trans hStep1 (Nat.mul_le_mul_right B (qsum_allGood64U_le B good hGood t))

private theorem filter_range_eq_qsum64U (good : Nat → Bool) :
    ((List.range 64).filter good).length =
      qsum 64 (fun i => if good i.1 = true then 1 else 0) := by
  have gen : ∀ n : Nat,
      ((List.range n).filter good).length = qsum n (fun i => if good i.1 = true then 1 else 0) := by
    intro n; induction n with
    | zero => rfl
    | succ n ihn =>
      rw [List.range_succ, List.filter_append, List.length_append, ihn,
          qsum_append_one n (fun u => if good u = true then 1 else 0)]
      dsimp only [List.filter, List.length]
      cases good n <;> simp
  exact gen 64

private theorem uncond128_verify_extract (x : WhirStmt QuinticGoldilocks)
    (m0 m1 : WhirMsg QuinticGoldilocks) (c0 c1 : Nat)
    (hv : (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x
      [(m0, c0), (m1, c1)] = true) :
    m0.poly.length ≤ 2 ∧ RoundPoly.evalCoeffs m0.poly CommRingOps.zero = x.claim ∧
    ∀ j < 102, RoundPoly.evalCoeffs m0.poly (zkHemV2Uncond128Env.domPt 0 ((c1 / 64 ^ j) % 64)) =
      x.table.getD ((c1 / 64 ^ j) % 64) CommRingOps.zero := by
  have hEq := whirOracleIop_verify_oneStage_noFold_eq zkHemV2Uncond128Env 6 quinticGoldilocksCard
    quinticGoldilocksCard_pos zkHemV2Uncond128Stage 616 rfl rfl rfl rfl x m0 m1 c0 c1
  dsimp only at hEq
  change (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x [(m0, c0), (m1, c1)] = _ at hEq
  rw [hEq] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  have hDeg : m0.poly.length ≤ 2 := hv.1.1.1.2
  have hZipQ := hv.1.2
  have hClaim : x.claim = RoundPoly.evalCoeffs m0.poly CommRingOps.zero := hv.2
  refine ⟨hDeg, hClaim.symm, fun j hj => ?_⟩
  let vals := (List.range 102).map (fun k =>
    x.table.getD ((c1 / 64 ^ k) % 64) CommRingOps.zero)
  have hjR : j < (List.range 102).length := by rw [List.length_range]; exact hj
  have hjV : j < vals.length := by dsimp only [vals]; rw [List.length_map, List.length_range]; exact hj
  have hMem : (j, x.table.getD ((c1 / 64 ^ j) % 64) CommRingOps.zero) ∈ (List.range 102).zip vals := by
    have hGet : ((List.range 102).zip vals)[j]'(by rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hjR, hjV⟩) =
        (j, x.table.getD ((c1 / 64 ^ j) % 64) CommRingOps.zero) := by
      dsimp only [vals]
      rw [List.getElem_zip, List.getElem_range, List.getElem_map, List.getElem_range]
    exact hGet ▸ List.getElem_mem _
  have hChk := List.all_eq_true.mp hZipQ _ hMem
  rw [decide_eq_true_eq] at hChk
  exact hChk

private theorem pow2_616_split : 2 ^ 616 = 2 ^ 4 * 64 ^ 102 := by
  calc 2 ^ 616 = 2 ^ (4 + 6 * 102) := rfl
    _ = 2 ^ 4 * (2 ^ 6) ^ 102 := by rw [Nat.pow_add, Nat.pow_mul]
    _ = 2 ^ 4 * 64 ^ 102 := rfl

private theorem qsum_eq_of_eq_u {n m : Nat} (h : n = m) (f : Nat → Nat) :
    qsum n (fun i => f i.1) = qsum m (fun j => f j.1) := by subst h; rfl

private theorem uncond128_round0_flips (x : WhirStmt QuinticGoldilocks)
    (m : WhirMsg QuinticGoldilocks) :
    qsum (2 ^ (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).w)
      (fun ch => if (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x
        ([] ++ [(m, ch.1)]) = true then 1 else 0) ≤ 0 := by
  have hW : 2 ^ (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).w = 2 ^ 616 := rfl
  rw [qsum_eq_of_eq_u hW (fun u => if (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x
    ([] ++ [(m, u)]) = true then 1 else 0)]
  dsimp only [List.nil_append]
  have hZero : ∀ ch : Fin (2 ^ 616),
      (if (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x [(m, ch.1)] = true then 1 else 0) = 0 := by
    intro ch; cases hv : (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x [(m, ch.1)]
    · rfl
    · exfalso; rw [OracleIop.verify_eq] at hv
      have hLen := of_decide_eq_true (Bool.and_eq_true_iff.mp hv).1
      have h2 : zkHemV2Uncond128Sched.numRounds = 2 := rfl; rw [h2] at hLen; simp at hLen
  rw [qsum_congr hZero, qsum_const, Nat.mul_zero]; exact Nat.le_refl 0

private theorem uncond128_round1_flips (x : WhirStmt QuinticGoldilocks)
    (hx : ¬ (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).inLang x)
    (m0 m : WhirMsg QuinticGoldilocks) (c0 : Nat) :
    qsum (2 ^ (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).w)
      (fun ch => if (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x
        ([(m0, c0)] ++ [(m, ch.1)]) = true then 1 else 0) ≤ 2 ^ 4 * 8 ^ 102 := by
  have hW : 2 ^ (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).w = 2 ^ 4 * 64 ^ 102 :=
    pow2_616_split
  rw [qsum_eq_of_eq_u hW (fun u => if (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x
    ([(m0, c0)] ++ [(m, u)]) = true then 1 else 0)]
  dsimp only [List.cons_append, List.nil_append]
  if hPolyOk : m0.poly.length ≤ 2 ∧ RoundPoly.evalCoeffs m0.poly CommRingOps.zero = x.claim then
    let goodPos (p : Nat) : Bool :=
      decide (RoundPoly.evalCoeffs m0.poly (zkHemV2Uncond128Env.domPt 0 p) =
        x.table.getD p CommRingOps.zero)
    have hGoodLe8 : qsum 64 (fun i => if goodPos i.1 = true then 1 else 0) ≤ 8 := by
      rcases Nat.lt_or_ge 8 (qsum 64 (fun i => if goodPos i.1 = true then 1 else 0)) with hGt8 | hLe8
      · exfalso
        have hGe9 : 9 ≤ agreeCount zkHemV2Uncond128Env 64 x.table m0.poly := by
          unfold agreeCount; rw [filter_range_eq_qsum64U goodPos]; exact hGt8
        exact hx ⟨m0.poly, hPolyOk.1, hGe9, hPolyOk.2⟩
      · exact hLe8
    have hCongr :
        qsum (2 ^ 4 * 64 ^ 102) (fun ch =>
          if (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x
            [(m0, c0), (m, ch.1)] = true then 1 else 0) ≤
        qsum (2 ^ 4 * 64 ^ 102) (fun ch =>
          if allGood64U goodPos 102 (ch.1 % (64 ^ 102)) = true then 1 else 0) := by
      refine qsum_le_qsum (fun ch => ?_)
      cases hv : (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x [(m0, c0), (m, ch.1)]
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact Nat.zero_le _
      · simp only [↓reduceIte]
        obtain ⟨_, _, hAllQ⟩ := uncond128_verify_extract x m0 m c0 ch.1 hv
        have hModAll : ∀ j < 102, goodPos (((ch.1 % (64 ^ 102)) / 64 ^ j) % 64) = true := by
          intro j hj
          have hPowSplit : 64 ^ 102 = 64 ^ j * (64 * 64 ^ (102 - j - 1)) := by
            calc 64 ^ 102 = 64 ^ (j + (102 - j - 1 + 1)) := congrArg (64 ^ ·) (by omega)
              _ = 64 ^ j * 64 ^ (102 - j - 1 + 1) := Nat.pow_add 64 j _
              _ = 64 ^ j * (64 ^ (102 - j - 1) * 64) := by rw [Nat.pow_succ]
              _ = 64 ^ j * (64 * 64 ^ (102 - j - 1)) := by rw [Nat.mul_comm (64 ^ (102 - j - 1)) 64]
          have hDivModEq : ∀ u : Nat, ((u % (64 ^ 102)) / 64 ^ j) % 64 = (u / 64 ^ j) % 64 := by
            intro u
            have hd : 64 ^ 102 * (u / 64 ^ 102) + u % 64 ^ 102 = u := Nat.div_add_mod u (64 ^ 102)
            generalize u / 64 ^ 102 = q102, u % 64 ^ 102 = r102 at hd ⊢
            rw [← hd, hPowSplit, Nat.mul_assoc (64 ^ j),
                Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 64)),
                Nat.mul_assoc 64, Nat.mul_add_mod]
          rw [hDivModEq ch.1]; exact decide_eq_true (hAllQ j hj)
        rw [allGood64U_of_range goodPos 102 _ hModAll]; exact Nat.le_refl 1
    rw [qsum_mul_div_mod_u (2 ^ 4) (64 ^ 102) (Nat.pow_pos (by decide))
      (fun _ r => if allGood64U goodPos 102 r = true then 1 else 0), qsum_const] at hCongr
    exact Nat.le_trans hCongr (Nat.mul_le_mul_left (2 ^ 4) (qsum_allGood64U_le 8 goodPos hGoodLe8 102))
  else
    have hZero : ∀ ch : Fin (2 ^ 4 * 64 ^ 102),
        (if (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x
          [(m0, c0), (m, ch.1)] = true then 1 else 0) = 0 := by
      intro ch
      cases hv : (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify x [(m0, c0), (m, ch.1)]
      · rfl
      · obtain ⟨hd, hc, _⟩ := uncond128_verify_extract x m0 m c0 ch.1 hv
        exact absurd ⟨hd, hc⟩ hPolyOk
    rw [qsum_congr hZero, qsum_const, Nat.mul_zero]; exact Nat.zero_le _

/-- **Unconditional 102-Query Quintic `WhirScheduleCert` (`zkHemV2Uncond128Cert`):**
    Clears `< 2^{-288}` per round with zero external assumptions. -/
def zkHemV2Uncond128Cert : WhirScheduleCert zkHemV2Uncond128Env zkHemV2Uncond128Sched 616 where
  cert := {
    state := (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify
    bad := fun r => if r.1 = 1 then 2 ^ 4 * 8 ^ 102 else 0
    init := fun x _ => by
      rw [OracleIop.verify_eq]
      have hF : decide (([] : List (WhirMsg QuinticGoldilocks × Nat)).length =
          zkHemV2Uncond128Sched.numRounds) = false := by decide
      rw [hF, Bool.false_and]
    accept := fun _ _ hv => hv
    flip := fun x hx r pref m hLen _ => by
      match r, pref, hLen with
      | ⟨0, _⟩, [], _ => exact Nat.le_trans (uncond128_round0_flips x m) (Nat.zero_le _)
      | ⟨0, _⟩, _ :: _, h => exact absurd h (by simp only [List.length_cons]; exact Nat.succ_ne_zero _)
      | ⟨1, _⟩, [], h => exact absurd h (show ¬ (0 : Nat) = 1 by decide)
      | ⟨1, _⟩, [(m0, c0)], _ =>
        exact Nat.le_trans (uncond128_round1_flips x hx m0 m c0) (Nat.le_of_eq (ite_eq_left rfl).symm)
      | ⟨1, _⟩, _ :: _ :: _, h =>
        exact absurd (Nat.succ.inj h) (by simp only [List.length_cons]; exact Nat.succ_ne_zero _)
      | ⟨n + 2, hn⟩, _, _ =>
        exact absurd hn (by have h2 : zkHemV2Uncond128Sched.numRounds = 2 := rfl; rw [h2]; omega)
  }
  covers := fun r => by
    have h2 : zkHemV2Uncond128Sched.numRounds = 2 := rfl
    rcases r with ⟨_ | _ | n, hn⟩
    · unfold RatBound.le
      have hZ : (if (0 : Nat) = 1 then 2 ^ 4 * 8 ^ 102 else 0) = 0 := rfl
      dsimp only; rw [hZ, Nat.zero_mul]; exact Nat.zero_le _
    · have hGet : zkHemV2Uncond128Sched.roundBounds.getD 1 RatBound.one =
          zkHemV2Uncond128Stage.shiftBound quinticGoldilocksCard quinticGoldilocksCard_pos := by
        rw [WhirVerifierSchedule.roundBounds_eq]
        unfold zkHemV2Uncond128Sched; dsimp only
        rw [stagesRoundBounds_cons, stagesRoundBounds_nil, List.append_nil, WhirStage.roundBounds_eq]
        rfl
      rw [hGet, WhirStage.shiftBound_eq]
      unfold RatBound.le RatBound.add
      have hO : (if (1 : Nat) = 1 then 2 ^ 4 * 8 ^ 102 else 0) = 2 ^ 4 * 8 ^ 102 := rfl
      have hDom : zkHemV2Uncond128Stage.domainSize = 64 := rfl
      have hQ : zkHemV2Uncond128Stage.queryCount = 102 := rfl
      have hAg : zkHemV2Uncond128Stage.agree + zkHemV2Uncond128Stage.foldK = 9 := rfl
      dsimp only; rw [hO, hDom, hQ, hAg, pow2_616_split]
      have hL : (2 ^ 4 * 8 ^ 102) * (64 ^ 102 * quinticGoldilocksCard) =
          (8 ^ 102 * quinticGoldilocksCard) * (2 ^ 4 * 64 ^ 102) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [hL]; refine Nat.mul_le_mul_right (2 ^ 4 * 64 ^ 102) ?_
      exact Nat.le_trans
        (Nat.mul_le_mul_right quinticGoldilocksCard (Nat.pow_le_pow_left (by decide) 102))
        (Nat.le_add_right _ _)
    · rw [h2] at hn; omega

theorem zkHemV2Uncond128_honest_accepts :
    (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify
      ⟨List.replicate 64 QuinticGoldilocks.one, QuinticGoldilocks.one⟩
      [(⟨[], [QuinticGoldilocks.one], []⟩, 0),
       (⟨[], [], List.replicate 5 QuinticGoldilocks.one⟩, 0)] = true := by
  have hEq := whirOracleIop_verify_oneStage_noFold_eq zkHemV2Uncond128Env 6 quinticGoldilocksCard
    quinticGoldilocksCard_pos zkHemV2Uncond128Stage 616 rfl rfl rfl rfl
    ⟨List.replicate 64 QuinticGoldilocks.one, QuinticGoldilocks.one⟩
    ⟨[], [QuinticGoldilocks.one], []⟩ ⟨[], [], List.replicate 5 QuinticGoldilocks.one⟩ 0 0
  dsimp only at hEq
  change (whirOracleIop zkHemV2Uncond128Env zkHemV2Uncond128Sched 616).verify _ _ = _ at hEq
  rw [hEq]; decide +kernel

private theorem filter_eq_nil_u128 {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: as, h => by
    rw [List.filter_cons, h a List.mem_cons_self]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact filter_eq_nil_u128 p as (fun b hb => h b (List.mem_cons_of_mem _ hb))

private theorem nodup_filter_eq_le_one_u128 {α : Type} [DecidableEq α] (w : α) :
    ∀ (pool : List α), pool.Nodup → (pool.filter (fun x => decide (x = w))).length ≤ 1
  | [], _ => Nat.zero_le 1
  | x :: xs, hNd => by
    obtain ⟨hxNotMem, hNdXs⟩ := List.nodup_cons.mp hNd
    if hEq : x = w then
      subst hEq
      have hRest : xs.filter (fun y => decide (y = x)) = [] :=
        filter_eq_nil_u128 _ xs (fun y hy => decide_eq_false (fun hyx => hxNotMem (hyx ▸ hy)))
      simp only [List.filter_cons, decide_true, ↓reduceIte, hRest, List.length_singleton]
      exact Nat.le_refl 1
    else
      simp only [List.filter_cons, decide_eq_false hEq, Bool.false_eq_true, ↓reduceIte]
      exact nodup_filter_eq_le_one_u128 w xs hNdXs

theorem zkHemV2Uncond128_false_not_inLang :
    ¬ whirInLang zkHemV2Uncond128Env zkHemV2Uncond128Sched
      ⟨List.replicate 64 QuinticGoldilocks.one, QuinticGoldilocks.zero⟩ := by
  rintro ⟨P, hLen, hAgree, hClaim⟩
  have hLen2 : P.length ≤ 2 := hLen
  have hAtMost1 : agreeCount zkHemV2Uncond128Env 64 (List.replicate 64 QuinticGoldilocks.one) P ≤ 1 := by
    have hCoeff1 : ∃ c1 : QuinticGoldilocks, ∀ z : QuinticGoldilocks,
        RoundPoly.evalCoeffs P z = z *ᵍ c1 := by
      rcases P with _ | ⟨c0, _ | ⟨c1, _ | ⟨_, _⟩⟩⟩
      · exact ⟨CommRingOps.zero, fun z => by dsimp only [RoundPoly.evalCoeffs]; constructive_ring⟩
      · have hc0 : c0 = CommRingOps.zero := by
          dsimp only [zkHemV2Uncond128Env, RoundPoly.evalCoeffs] at hClaim
          calc c0 = c0 +ᵍ CommRingOps.zero *ᵍ CommRingOps.zero := by constructive_ring
            _ = CommRingOps.zero := hClaim
        subst hc0
        exact ⟨CommRingOps.zero, fun z => by dsimp only [RoundPoly.evalCoeffs]; constructive_ring⟩
      · have hc0 : c0 = CommRingOps.zero := by
          dsimp only [zkHemV2Uncond128Env, RoundPoly.evalCoeffs] at hClaim
          calc c0 = c0 +ᵍ CommRingOps.zero *ᵍ (c1 +ᵍ CommRingOps.zero *ᵍ CommRingOps.zero) := by
                  constructive_ring
            _ = CommRingOps.zero := hClaim
        subst hc0
        exact ⟨c1, fun z => by dsimp only [RoundPoly.evalCoeffs]; constructive_ring⟩
      · exfalso; simp only [List.length_cons] at hLen2; omega
    obtain ⟨c1, hEval⟩ := hCoeff1
    have hRepGetD : ∀ {p : Nat}, p < 64 →
        (List.replicate 64 QuinticGoldilocks.one).getD p CommRingOps.zero = QuinticGoldilocks.one := by
      intro p hp; rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      simp only [hp, ↓reduceIte, Option.getD_some]
    if hc1 : c1 = CommRingOps.zero then
      subst hc1; unfold agreeCount
      have hNil : (List.range 64).filter (fun p =>
          decide (RoundPoly.evalCoeffs P (zkHemV2Uncond128Env.domPt 0 p) =
            (List.replicate 64 QuinticGoldilocks.one).getD p CommRingOps.zero)) = [] := by
        refine filter_eq_nil_u128 _ (List.range 64) (fun p hp => decide_eq_false (fun hEq => ?_))
        rw [hEval, LawfulCommRing.mul_zero, hRepGetD (List.mem_range.mp hp)] at hEq
        exact LawfulField.zero_ne_one hEq
      rw [hNil]; exact Nat.zero_le 1
    else
      unfold agreeCount
      have hMapEq : quinticCoset64 = (List.range 64).map (zkHemV2Uncond128Env.domPt 0) := by
        apply List.ext_getElem
        · rw [quinticCoset64_length, List.length_map, List.length_range]
        · intro i hi1 _; rw [List.getElem_map, List.getElem_range]
          dsimp only [zkHemV2Uncond128Env]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some]
      have hSub : ∀ r : List Nat, (∀ p ∈ r, p < 64) →
          (r.filter (fun p => decide (RoundPoly.evalCoeffs P (zkHemV2Uncond128Env.domPt 0 p) =
            (List.replicate 64 QuinticGoldilocks.one).getD p CommRingOps.zero))).length ≤
          ((r.map (zkHemV2Uncond128Env.domPt 0)).filter
            (fun z => decide (z = LawfulField.inv c1))).length := by
        intro r; induction r with
        | nil => intro _; exact Nat.le_refl 0
        | cons p ps ih =>
          intro hr
          have hpLt := hr p List.mem_cons_self
          have ihPs := ih (fun q hq => hr q (List.mem_cons_of_mem _ hq))
          simp only [List.filter_cons, List.map_cons]
          if hHit : RoundPoly.evalCoeffs P (zkHemV2Uncond128Env.domPt 0 p) =
              (List.replicate 64 QuinticGoldilocks.one).getD p CommRingOps.zero then
            have hInv : zkHemV2Uncond128Env.domPt 0 p = LawfulField.inv c1 := by
              have hHit1 := hHit; rw [hEval, hRepGetD hpLt] at hHit1
              calc zkHemV2Uncond128Env.domPt 0 p
                  = (zkHemV2Uncond128Env.domPt 0 p *ᵍ c1) *ᵍ LawfulField.inv c1 := by
                      rw [LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hc1, LawfulCommRing.mul_one]
                _ = LawfulField.inv c1 := by rw [hHit1]; exact LawfulCommRing.one_mul _
            rw [decide_eq_true hHit, decide_eq_true hInv]
            simp only [↓reduceIte, List.length_cons]; exact Nat.succ_le_succ ihPs
          else
            rw [decide_eq_false hHit]; simp only [Bool.false_eq_true, ↓reduceIte]
            cases decide (zkHemV2Uncond128Env.domPt 0 p = LawfulField.inv c1) <;>
              simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
            · exact ihPs
            · exact Nat.le_trans ihPs (Nat.le_succ _)
      have hBound := hSub (List.range 64) (fun _ hp => List.mem_range.mp hp)
      rw [← hMapEq] at hBound
      exact Nat.le_trans hBound (nodup_filter_eq_le_one_u128 _ quinticCoset64 quinticCoset64_nodup)
  have h9 : 9 ≤ agreeCount zkHemV2Uncond128Env 64 (List.replicate 64 QuinticGoldilocks.one) P := hAgree
  omega

/-- Single-proof (`d = 0`) & `(2^{d+1} - 1)`-node (`d ≤ 16`) `< 2^{-128}` QROM bound at `Q ≤ 2^{64}`. -/
theorem zkHemV2Uncond128_tree_qrom_lt_128_at_2pow64
    (prof : WhirCommitmentProfile) {d Q : Nat} (hd : d ≤ 16) (hQ : Q ≤ 2 ^ 64) :
    RatBound.lt
      (RatBound.add
        (RatBound.scale (2 ^ (d + 1) - 1) (scheduleQromError zkHemV2Uncond128Sched Q))
        (merkleProfileQromBound prof Q))
      (RatBound.invPow2 128) := by
  have hNodesLe : 2 ^ (d + 1) - 1 ≤ 131071 := by
    have hPow : 2 ^ (d + 1) ≤ 2 ^ 17 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hScaleMono : RatBound.le
      (RatBound.scale (2 ^ (d + 1) - 1) (scheduleQromError zkHemV2Uncond128Sched Q))
      (RatBound.scale 131071 (scheduleQromError zkHemV2Uncond128Sched (2 ^ 64))) := by
    have h1 : RatBound.le
        (RatBound.scale (2 ^ (d + 1) - 1) (scheduleQromError zkHemV2Uncond128Sched Q))
        (RatBound.scale 131071 (scheduleQromError zkHemV2Uncond128Sched Q)) := by
      let e := scheduleQromError zkHemV2Uncond128Sched Q
      show (2 ^ (d + 1) - 1) * e.num * e.den ≤ 131071 * e.num * e.den
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hNodesLe)
    have h2 : RatBound.le
        (RatBound.scale 131071 (scheduleQromError zkHemV2Uncond128Sched Q))
        (RatBound.scale 131071 (scheduleQromError zkHemV2Uncond128Sched (2 ^ 64))) := by
      have hm := scheduleQromError_mono zkHemV2Uncond128Sched hQ
      let e1 := scheduleQromError zkHemV2Uncond128Sched Q
      let e2 := scheduleQromError zkHemV2Uncond128Sched (2 ^ 64)
      show 131071 * e1.num * e2.den ≤ 131071 * e2.num * e1.den
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 131071 hm
    exact RatBound.le_trans h1 h2
  have hMerkleMono := RatBound.le_trans (merkleProfileQromBound_mono prof hQ)
    (merkleProfileQromBound_le_400 prof (2 ^ 64))
  have hTop : RatBound.lt
      (RatBound.add
        (RatBound.scale 131071 (scheduleQromError zkHemV2Uncond128Sched (2 ^ 64)))
        (merkle400QromBound (2 ^ 64)))
      (RatBound.invPow2 128) := by
    rw [scheduleQromError_eq, WhirVerifierSchedule.roundBounds_eq]
    unfold zkHemV2Uncond128Sched; dsimp only
    rw [stagesRoundBounds_cons, stagesRoundBounds_nil, List.append_nil, WhirStage.roundBounds_eq,
        WhirStage.oodBound_eq, WhirStage.shiftBound_eq]
    dsimp only [zkHemV2Uncond128Stage, List.replicate, List.nil_append, List.map]
    rw [binom2_eq]; decide +kernel
  exact ratBound_lt_of_le_of_lt_packed (RatBound.add_le_add hScaleMono hMerkleMono) hTop

/-! ## §2. Unified `.xmssPoseidon2` & `.corduroyPoseidon2` `StepOp256` Committee Extraction -/

/-- Supported deployed hash-based validator signature profiles. -/
@[expose] def IsDeployedAggProfile (profile : AggSigProfile) : Prop :=
  profile = .xmssPoseidon2 ∨ profile = .corduroyPoseidon2

/-- Native signature geometry corresponding to `profile`. -/
@[expose] def profileGeom : AggSigProfile → AggSigGeometry
  | .xmssPoseidon2 => xmssPoseidon2Geom
  | .corduroyPoseidon2 => corduroyPoseidon2Geom

/-- Extract slot `slotIdx`'s native signature from `rows` for either `.xmssPoseidon2` or `.corduroyPoseidon2`. -/
@[expose] def extractSlotNativeSig (profile : AggSigProfile) (rows : List StepOpRow)
    (slotIdx : Nat) : AggNativeSignature :=
  match profile with
  | .xmssPoseidon2 => stepXmssSig (stepOpSlotRow .xmssPoseidon2 rows slotIdx)
  | .corduroyPoseidon2 => stepCordSig (stepOpSlotRow .corduroyPoseidon2 rows slotIdx)

/-- Public slot vector derived from an `AggregateStatement` for `stepOp256TableOk`. -/
@[expose] def succinctCommitteeSlots {nVal : Nat}
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) : List StepOpSlot :=
  (List.finRange nVal).map fun i =>
    if stmt.bitmap.getLsbD i.val then
      some (stmt.roster i, computeMessageMu (stmt.roster i) stmt.message)
    else
      none

private theorem finRange_getElem?_local (n k : Nat) (hk : k < n) :
    (List.finRange n)[k]? = some ⟨k, hk⟩ := by
  have hLen : (List.finRange n).length = n := List.length_finRange
  have hk' : k < (List.finRange n).length := by rw [hLen]; exact hk
  rw [List.getElem?_eq_getElem hk', List.getElem_finRange]
  rfl

theorem succinctCommitteeSlots_getElem? {nVal : Nat}
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (k : Nat) (hk : k < nVal) :
    (succinctCommitteeSlots stmt)[k]? =
      some (if stmt.bitmap.getLsbD k then
        some (stmt.roster ⟨k, hk⟩, computeMessageMu (stmt.roster ⟨k, hk⟩) stmt.message)
      else none) := by
  unfold succinctCommitteeSlots
  rw [List.getElem?_map, finRange_getElem?_local nVal k hk]
  rfl

/-- **Unified `.xmssPoseidon2` + `.corduroyPoseidon2` `StepOp256` Extraction (`stepOp256TableOk_bothProfiles_extract`):**
    Connects both `stepOp256TableOk_xmss_extract` and `stepOp256TableOk_corduroy_extract` to `Spec.ValidAggregateWitness`. -/
theorem stepOp256TableOk_bothProfiles_extract {nVal : Nat}
    (profile : AggSigProfile) (hDep : IsDeployedAggProfile profile)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal)
    (rows : List StepOpRow)
    (hProfAll : (List.finRange nVal).all (fun i =>
      !stmt.bitmap.getLsbD i.val || ((stmt.roster i).profile == profile)) = true)
    (hTable : stepOp256TableOk profile (succinctCommitteeSlots stmt) rows = true) :
    Spec.ValidAggregateWitness (verifyAggNativeSig (profileGeom profile)) stmt
      (fun i => some (extractSlotNativeSig profile rows i.val)) := by
  refine Spec.ValidAggregateWitness.intro (fun i hAct => ?_)
  refine ⟨extractSlotNativeSig profile rows i.val, rfl, ?_⟩
  have hProfMem := List.all_eq_true.mp hProfAll i (List.mem_finRange i)
  rw [hAct] at hProfMem
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hProfMem
  have hSlot : (succinctCommitteeSlots stmt)[i.val]? =
      some (some (stmt.roster i, computeMessageMu (stmt.roster i) stmt.message)) := by
    rw [succinctCommitteeSlots_getElem? stmt i.val i.isLt]
    have hFinEq : (⟨i.val, i.isLt⟩ : Fin nVal) = i := Fin.ext rfl
    rw [hFinEq, hAct]; simp only [↓reduceIte]
  rcases hDep with rfl | rfl
  · exact stepOp256TableOk_xmss_extract (succinctCommitteeSlots stmt) rows i.val
      (stmt.roster i, computeMessageMu (stmt.roster i) stmt.message) stmt.message
      hTable hSlot hProfMem rfl
  · exact stepOp256TableOk_corduroy_extract (succinctCommitteeSlots stmt) rows i.val
      (stmt.roster i, computeMessageMu (stmt.roster i) stmt.message) stmt.message
      hTable hSlot hProfMem rfl

/-- Single-slot `StepOp256` extraction for slot `i`'s isolated row slice `slotRows`. -/

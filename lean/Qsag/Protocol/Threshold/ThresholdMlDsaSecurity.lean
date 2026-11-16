module
/-
# Threshold ML-DSA Abort-Transcript Zero-Knowledge, ML-DSA-65/87 Parameters & RSS Refinement

Constructive arithmetic and conditional view-simulation proofs accompanying
`Qsag.ThresholdMlDsaAndToprf`. Both the four-lane (`ML-DSA-44`) and rectangular (`ML-DSA-44/65/87`,
`(k, ℓ) = (4, 4), (6, 5), (8, 7)`) trace theorems receive the real secret-dependent outcome list:
they prove pad hiding conditional on that list, not a simulator for its accept/reject or retry-count
distribution.
1. **NIST FIPS 204 `ML-DSA-44`, `ML-DSA-65`, and `ML-DSA-87` (`PQ128`) Parameter Verification**:
   Algebraic and byte-wire consistency (`mlDsa_all_three_levels_wellFormed`), `η = 4` DKG nibble
   rejection (`eta4SampleNibble_bijective_on_range`), `γ₂ = 261888` mod-16 `HighBits` wrap
   (`mlDsa65_87_highBits_bounds`), and challenge entropy `2^192 < challengeSpaceCard 39`,
   `2^225 < challengeSpaceCard 49`, `2^256 < challengeSpaceCard 60` (`mlDsa_challenge_entropy_bounds`).
2. **Multi-Attempt Sealed-`w₁` Abort-Transcript Zero-Knowledge (`threshold_mldsa_abort_transcript_zk`)**:
   Keeping `w₁` and `c` secret-shared inside RSS until all rejection predicates pass opens zero
   `w₁`, `c`, `z`, or `h` on rejected attempts; across `R`-attempt traces the joint view is
   simulated from `(A, t₁)` and public outcomes alone, paired with `fips204_z_plateau_shift_invariant`
   and `tooth_unsealed_w1_or_irwin_hall_abort_leaks_secret`.
3. **3-Party `(2, 3)` RSS Multiplication + Sacrifice Refinement & `C(n, t - 1)` PRSS Hybrid**:
   Proves `rss3MulStep_recon`, `rss3_repeated_sacrifice_pq256` (`2^256 < mldsaQ^12`), multi-turn
   `rss_distributed_trace_refines_sacrificedSignStep`, and `rss_prss_choose_hybrid`.
4. **Asymmetric `[-γ₁ + 1, γ₁]` Mask Boundary & Rectangular `ML-DSA-44/65/87` Abort-Transcript ZK**:
   Proves shift-invariance over the exact `2γ₁`-point FIPS 204 `ExpandMask` support `[-γ₁ + 1, γ₁]`
   (`fips204_asymmetric_2gamma1_plateau_shift_invariant`), refutes closed-box `≤ γ₁ - β` relaxation
   at the negative boundary (`tooth_closed_box_le_breaks_asymmetric_2gamma1_plateau`), proves
   `γ₂ = 261888` hint recovery (`useHint32_makeHint32_eq_highBits32`), and extends multi-attempt
   sealed-`w₁` view simulation to rectangular `(k, ℓ) = (4, 4), (6, 5), (8, 7)`
   (`threshold_mldsa_rect_abort_transcript_zk`, `threshold_mldsa65_abort_transcript_zk`,
   `threshold_mldsa87_abort_transcript_zk`).
-/

public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
public import Qsag.Tactic.AssuranceKit
public import Qsag.Math.Tactic.MaskBijection
import Qsag.Protocol.Aggregation.UcGames
import Qsag.Protocol.Credentials.AdvancedMpcAndCreds
import Qsag.Math.Goldilocks
import Qsag.Math.Lattices
import Qsag.Math.Counting
import Qsag.Math.CoeffPoly
import Qsag.Math.PolyRing
import Qsag.Math.HasseHensel

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

private theorem nat_lt_of_mul_lt_mul_right {a b c : Nat} (h : a * c < b * c) : a < b :=
  if hab : a < b then hab
  else False.elim (Nat.lt_irrefl (b * c)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right c (Nat.le_of_not_lt hab)) h))

private theorem ite_true {α : Sort _} {P : Prop} [Decidable P] (h : P) (a b : α) :
    (if P then a else b) = a := by
  cases ‹Decidable P› with
  | isTrue _ => rfl
  | isFalse hnp => exact absurd h hnp

private theorem ite_false {α : Sort _} {P : Prop} [Decidable P] (h : ¬ P) (a b : α) :
    (if P then a else b) = b := by
  cases ‹Decidable P› with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

/-! ## §1. NIST FIPS 204 `ML-DSA-44`, `ML-DSA-65` (Category 3) & `ML-DSA-87` (`PQ128`) Parameters -/

structure MlDsaLevelSpec where
  k : Nat
  ell : Nat
  gamma1 : Nat
  gamma2 : Nat
  tau : Nat
  eta : Nat
  beta : Nat
  omega : Nat
  highMod : Nat
  cTildeBytes : Nat
  zPolyBytes : Nat
  pkBytes : Nat
  sigBytes : Nat
  deriving DecidableEq, Repr

def mlDsa44Spec : MlDsaLevelSpec :=
  { k := 4, ell := 4, gamma1 := 131072, gamma2 := 95232, tau := 39, eta := 2,
    beta := 78, omega := 80, highMod := 44, cTildeBytes := 32, zPolyBytes := 576,
    pkBytes := 1312, sigBytes := 2420 }

def mlDsa65Spec : MlDsaLevelSpec :=
  { k := 6, ell := 5, gamma1 := 524288, gamma2 := 261888, tau := 49, eta := 4,
    beta := 196, omega := 55, highMod := 16, cTildeBytes := 48, zPolyBytes := 640,
    pkBytes := 1952, sigBytes := 3309 }

def mlDsa87Spec : MlDsaLevelSpec :=
  { k := 8, ell := 7, gamma1 := 524288, gamma2 := 261888, tau := 60, eta := 2,
    beta := 120, omega := 75, highMod := 16, cTildeBytes := 64, zPolyBytes := 640,
    pkBytes := 2592, sigBytes := 4627 }

def mlDsaLevelWellFormed (p : MlDsaLevelSpec) : Bool :=
  decide (p.beta = p.tau * p.eta) &&
  decide (mldsaQ - 1 = p.highMod * (2 * p.gamma2)) &&
  decide (p.beta < p.gamma1) && decide (p.beta < p.gamma2) &&
  decide (0 < p.omega ∧ p.omega ≤ 256 * p.k) &&
  decide (p.pkBytes = 32 + 320 * p.k) &&
  decide (p.sigBytes = p.cTildeBytes + p.ell * p.zPolyBytes + p.omega + p.k)

theorem mlDsa_all_three_levels_wellFormed :
    mlDsaLevelWellFormed mlDsa44Spec = true ∧
    mlDsaLevelWellFormed mlDsa65Spec = true ∧
    mlDsaLevelWellFormed mlDsa87Spec = true := by decide

theorem tooth_mlDsaLevelWellFormed_bad_beta :
    ∃ p : MlDsaLevelSpec, p.beta ≠ p.tau * p.eta ∧ mlDsaLevelWellFormed p = false :=
  ⟨{ mlDsa87Spec with beta := 119 }, by decide, by decide⟩

/-- FIPS 204 `η = 4` DKG nibble rejection (`threshold_mldsa.rs`: `b < 9 => 4 - b`). -/
def eta4SampleNibble (b : Fin 16) : Option Int :=
  if b.val < 9 then some (4 - Int.ofNat b.val) else none

theorem eta4SampleNibble_bijective_on_range :
    qsum 16 (fun b => if eta4SampleNibble b ≠ none then 1 else 0) = 9 ∧
    ∀ target : Int, -4 ≤ target → target ≤ 4 →
      qsum 16 (fun b => if eta4SampleNibble b = some target then 1 else 0) = 1 := by
  refine ⟨by decide, fun target hLo hHi => ?_⟩
  have hCases :
      target = -4 ∨ target = -3 ∨ target = -2 ∨ target = -1 ∨ target = 0 ∨
      target = 1 ∨ target = 2 ∨ target = 3 ∨ target = 4 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- FIPS 204 `HighBits(r, 2 γ₂)` at `γ₂ = (q - 1) / 32 = 261888` (`α = 523776 = 512 * 1023`). -/
def fips204HighBits32 (r : Fq204) : Nat :=
  if mldsaQ - 1 - 261888 < r.val then 0 else (r.val + 261887) / 523776

theorem mlDsa65_87_highBits_bounds (r : Fq204) :
    fips204HighBits32 r < 16 ∧
    fips204HighBits32 r = ((r.val + 261887) / 523776) % 16 ∧
    fips204HighBits32 r = (((r.val + 261887) / 512) / 1023) % 16 := by
  unfold fips204HighBits32
  have hr := r.isLt; unfold mldsaQ at hr ⊢
  have hDiv512 : ((r.val + 261887) / 512) / 1023 = (r.val + 261887) / 523776 := by
    rw [Nat.div_div_eq_div_mul]
  rw [hDiv512]
  if hWrap : 8380417 - 1 - 261888 < r.val then
    rw [ite_true hWrap]
    have hQuot : (r.val + 261887) / 523776 = 16 := by omega
    rw [hQuot]; decide
  else
    rw [ite_false hWrap]
    have hLt16 : (r.val + 261887) / 523776 < 16 := by omega
    exact ⟨hLt16, (Nat.mod_eq_of_lt hLt16).symm, (Nat.mod_eq_of_lt hLt16).symm⟩

def binomRec : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomRec n k + binomRec n (k + 1)

def factRec : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factRec k

def descFact : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => (n + 1) * descFact n k

private theorem descFact_step_right :
    ∀ n k : Nat, descFact n (k + 1) + (k + 1) * descFact n k = (n + 1) * descFact n k
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | n + 1, 0 => by simp [descFact, Nat.mul_one, Nat.succ_mul]
  | n + 1, k + 1 => by
    have ih := descFact_step_right n k
    dsimp only [descFact]
    rw [Nat.succ_mul (k + 1), Nat.succ_mul (n + 1), ← Nat.add_assoc,
        Nat.mul_left_comm (k + 1) (n + 1), ← Nat.left_distrib (n + 1), ih]

theorem binomRec_mul_fact : ∀ n k : Nat, binomRec n k * factRec k = descFact n k
  | _, 0 => by simp [binomRec, factRec, descFact]
  | 0, _ + 1 => Nat.zero_mul _
  | n + 1, k + 1 => by
    simp only [binomRec, factRec, descFact]; rw [Nat.right_distrib]
    have h1 : binomRec n k * ((k + 1) * factRec k) = (k + 1) * (binomRec n k * factRec k) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (binomRec n k) (k + 1), Nat.mul_assoc]
    have h2 : binomRec n (k + 1) * ((k + 1) * factRec k) = binomRec n (k + 1) * factRec (k + 1) := rfl
    rw [h1, h2, binomRec_mul_fact n k, binomRec_mul_fact n (k + 1), Nat.add_comm]
    exact descFact_step_right n k

def challengeSpaceCard (tau : Nat) : Nat := 2 ^ tau * binomRec 256 tau

private theorem challengeSpaceCard_gt_pow2 (tau bits : Nat)
    (h : 2 ^ bits * factRec tau < 2 ^ tau * descFact 256 tau) :
    2 ^ bits < challengeSpaceCard tau := by
  apply nat_lt_of_mul_lt_mul_right (c := factRec tau)
  unfold challengeSpaceCard; rw [Nat.mul_assoc, binomRec_mul_fact]; exact h

/-- **FIPS 204 Challenge Entropy Bounds (`mlDsa_challenge_entropy_bounds`)**:
    `ML-DSA-44` (`> 2^192`), `ML-DSA-65` (`> 2^225`), `ML-DSA-87` (`> 2^256`, `≥ 128` Grover bits). -/
theorem mlDsa_challenge_entropy_bounds :
    2 ^ 192 < challengeSpaceCard mlDsa44Spec.tau ∧
    2 ^ 225 < challengeSpaceCard mlDsa65Spec.tau ∧
    2 ^ 256 < challengeSpaceCard mlDsa87Spec.tau :=
  ⟨challengeSpaceCard_gt_pow2 39 192 (by decide),
   challengeSpaceCard_gt_pow2 49 225 (by decide),
   challengeSpaceCard_gt_pow2 60 256 (by decide)⟩

/-! ## §2. Sealed-`w₁` Multi-Attempt Abort-Transcript Zero-Knowledge -/

private theorem fq204_inv_mul_cancel {a : Fq204} (ha : a ≠ Fq204.zero) :
    Fq204.mul (Fq204.inv a) a = Fq204.one := by
  rw [Fq204.mul_comm, Fq204.mul_inv_cancel ha]

def ext6ScaleEquiv (v : Fq204) (hv : v ≠ Fq204.zero) : SimpleEquiv Ext6Fq204 Ext6Fq204 where
  toFun b := ext6Scale b v
  invFun u := ext6Scale u (Fq204.inv v)
  left_inv x := by rw [ext6Scale_mul, Fq204.mul_inv_cancel hv, ext6Scale_one]
  right_inv x := by rw [ext6Scale_mul, fq204_inv_mul_cancel hv, ext6Scale_one]

def bv256XorEquiv (target : BitVec 256) : SimpleEquiv (BitVec 256) (BitVec 256) where
  toFun m := target ^^^ m
  invFun v := target ^^^ v
  left_inv m := bv_xor_cancel_left target m
  right_inv v := bv_xor_cancel_left target v

structure SealedAttemptPads where
  maskW : PolyVec4
  maskZ : PolyVec4
  maskLow : PolyVec4
  maskBin : BitVec 256
  verdictBlind : Ext6Fq204

structure SealedSignAttemptView where
  openedW : PolyVec4
  openedZ : PolyVec4
  openedLow : PolyVec4
  openedBin : BitVec 256
  openedVerdict : Ext6Fq204
  released : Option ((Fin 4 → NatTree 8) × ThresholdSignSig)

def sealedAcceptBool
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 y : PolyVec4) (mu : List UInt8) : Bool :=
  let t := addVec4 (matVecMul4 A s1) s2
  let t0 := power2RoundLowVec4 t
  let w := matVecMul4 A y
  let w1 := highBitsVec4 w
  let c := sampleInBall (chalHash mu w1)
  let z := addVec4 y (mulPolyVec4 c s1)
  let u := subVec4 w (mulPolyVec4 c s2)
  let ct0 := mulPolyVec4 c t0
  let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
  decide (infNormVec4 ct0 < mldsa44Gamma2) &&
  decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
  decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
  decide (hintWeightVec4 h ≤ mldsa44Omega)

def realSealedAttemptView
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 y : PolyVec4) (mu : List UInt8) (attempt : Nat)
    (keccakTraceBits : BitVec 256) (failTag : Fq204)
    (pads : SealedAttemptPads) : SealedSignAttemptView :=
  let t := addVec4 (matVecMul4 A s1) s2
  let t0 := power2RoundLowVec4 t
  let w := matVecMul4 A y
  let w1 := highBitsVec4 w
  let cTilde := chalHash mu w1
  let c := sampleInBall cTilde
  let z := addVec4 y (mulPolyVec4 c s1)
  let u := subVec4 w (mulPolyVec4 c s2)
  let ct0 := mulPolyVec4 c t0
  let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
  let accept := sealedAcceptBool chalHash sampleInBall A s1 s2 y mu
  { openedW := addVec4 w pads.maskW, openedZ := addVec4 z pads.maskZ,
    openedLow := addVec4 u pads.maskLow, openedBin := keccakTraceBits ^^^ pads.maskBin,
    openedVerdict := if accept then ext6Zero else ext6Scale pads.verdictBlind failTag,
    released := if accept then
      some (w1, { cTilde := cTilde, z := z, h := h, usedAttempt := attempt }) else none }

abbrev SimAttemptOutcome := Option ThresholdSignSig

def thresholdMlDsaAttemptSimulator
    (sampleInBall : List UInt8 → Poly256) (A : PolyMat4) (t1Scaled : PolyVec4)
    (out : SimAttemptOutcome) (pads : SealedAttemptPads) : SealedSignAttemptView :=
  match out with
  | none =>
    { openedW := pads.maskW, openedZ := pads.maskZ, openedLow := pads.maskLow,
      openedBin := pads.maskBin, openedVerdict := pads.verdictBlind, released := none }
  | some sig =>
    let c := sampleInBall sig.cTilde
    let w1Sim := useHintVec4 sig.h (subVec4 (matVecMul4 A sig.z) (mulPolyVec4 c t1Scaled))
    { openedW := pads.maskW, openedZ := pads.maskZ, openedLow := pads.maskLow,
      openedBin := pads.maskBin, openedVerdict := ext6Zero, released := some (w1Sim, sig) }

def sealedPadsTupleEquiv :
    SimpleEquiv SealedAttemptPads
      (PolyVec4 × PolyVec4 × PolyVec4 × BitVec 256 × Ext6Fq204) where
  toFun p := (p.maskW, p.maskZ, p.maskLow, p.maskBin, p.verdictBlind)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv := fun ⟨_, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _⟩ => rfl

def sealedAttemptPadEquiv
    (w z u : PolyVec4) (keccakTraceBits : BitVec 256)
    (accept : Bool) (failTag : Fq204) (hFail : failTag ≠ Fq204.zero) :
    SimpleEquiv SealedAttemptPads SealedAttemptPads :=
  let verdictEquiv : SimpleEquiv Ext6Fq204 Ext6Fq204 :=
    if accept then SimpleEquiv.refl _ else ext6ScaleEquiv failTag hFail
  SimpleEquiv.trans sealedPadsTupleEquiv
    (SimpleEquiv.trans
      (SimpleEquiv.prodCongr (rssMaskAddEquiv w)
        (SimpleEquiv.prodCongr (rssMaskAddEquiv z)
          (SimpleEquiv.prodCongr (rssMaskAddEquiv u)
            (SimpleEquiv.prodCongr (bv256XorEquiv keccakTraceBits) verdictEquiv))))
      (SimpleEquiv.symm sealedPadsTupleEquiv))

def sealedStepPadEquiv
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 y : PolyVec4) (mu : List UInt8)
    (keccakTraceBits : BitVec 256) (failTag : Fq204) (hFail : failTag ≠ Fq204.zero) :
    SimpleEquiv SealedAttemptPads SealedAttemptPads :=
  let w := matVecMul4 A y
  let c := sampleInBall (chalHash mu (highBitsVec4 w))
  sealedAttemptPadEquiv w (addVec4 y (mulPolyVec4 c s1)) (subVec4 w (mulPolyVec4 c s2))
    keccakTraceBits (sealedAcceptBool chalHash sampleInBall A s1 s2 y mu) failTag hFail

def sealedAttemptPublicOutcome
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 y : PolyVec4) (mu : List UInt8) (attempt : Nat) : SimAttemptOutcome :=
  let t := addVec4 (matVecMul4 A s1) s2
  let t0 := power2RoundLowVec4 t
  let w := matVecMul4 A y
  let w1 := highBitsVec4 w
  let cTilde := chalHash mu w1
  let c := sampleInBall cTilde
  let z := addVec4 y (mulPolyVec4 c s1)
  let u := subVec4 w (mulPolyVec4 c s2)
  let ct0 := mulPolyVec4 c t0
  let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
  if sealedAcceptBool chalHash sampleInBall A s1 s2 y mu then
    some { cTilde := cTilde, z := z, h := h, usedAttempt := attempt }
  else none

theorem sealedAttempt_sim_eq_real
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 y : PolyVec4) (mu : List UInt8) (attempt : Nat)
    (keccakTraceBits : BitVec 256) (failTag : Fq204)
    (hFail : failTag ≠ Fq204.zero) (pads : SealedAttemptPads) :
    thresholdMlDsaAttemptSimulator sampleInBall A
      (power2RoundHighVec4 (addVec4 (matVecMul4 A s1) s2))
      (sealedAttemptPublicOutcome chalHash sampleInBall A s1 s2 y mu attempt)
      ((sealedStepPadEquiv chalHash sampleInBall A s1 s2 y mu keccakTraceBits failTag hFail).toFun pads) =
    realSealedAttemptView chalHash sampleInBall A s1 s2 y mu attempt keccakTraceBits failTag pads := by
  unfold realSealedAttemptView sealedAttemptPublicOutcome thresholdMlDsaAttemptSimulator sealedStepPadEquiv
  dsimp only
  cases hAcc : sealedAcceptBool chalHash sampleInBall A s1 s2 y mu with
  | false =>
    simp only [sealedAttemptPadEquiv, SimpleEquiv.trans, SimpleEquiv.prodCongr,
      SimpleEquiv.symm, sealedPadsTupleEquiv, rssMaskAddEquiv_toFun, rssMaskAddEquiv_invFun, bv256XorEquiv,
      ext6ScaleEquiv, Bool.false_eq_true, ↓reduceIte]
  | true =>
    unfold sealedAcceptBool at hAcc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAcc
    rcases hAcc with ⟨⟨⟨hCt0, _⟩, hDiff⟩, _⟩
    have hB : mldsa44Gamma2 - mldsa44Beta ≤ 95232 := by decide
    let w := matVecMul4 A y
    let c := sampleInBall (chalHash mu (highBitsVec4 w))
    let u := subVec4 w (mulPolyVec4 c s2)
    obtain ⟨hLow, hHighEq⟩ := (centeredDiffNormVec4_lt_iff u w hB).mp hDiff
    have hUseHint := highBits_az_sub_ct_eq_w1 A s1 s2 y c mldsa44Beta hLow hCt0
    dsimp only at hUseHint
    have hW1Eq := hUseHint.trans hHighEq
    simp only [sealedAttemptPadEquiv, SimpleEquiv.trans, SimpleEquiv.prodCongr,
      SimpleEquiv.symm, SimpleEquiv.refl, sealedPadsTupleEquiv, rssMaskAddEquiv_toFun, rssMaskAddEquiv_invFun, bv256XorEquiv,
      ↓reduceIte]
    dsimp only [w, c] at hW1Eq
    rw [hW1Eq]

structure SealedAttemptStepSpec where
  y : PolyVec4
  attempt : Nat
  keccakTraceBits : BitVec 256
  failTag : Fq204

def realSealedSignTrace
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 : PolyVec4) (mu : List UInt8) :
    (steps : List SealedAttemptStepSpec) → (Fin steps.length → SealedAttemptPads) →
    List SealedSignAttemptView
  | [], _ => []
  | stp :: rest, padFn =>
    realSealedAttemptView chalHash sampleInBall A s1 s2 stp.y mu stp.attempt
      stp.keccakTraceBits stp.failTag (padFn ⟨0, Nat.zero_lt_succ _⟩) ::
    realSealedSignTrace chalHash sampleInBall A s1 s2 mu rest
      (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

def thresholdMlDsaTraceSimulator
    (sampleInBall : List UInt8 → Poly256) (A : PolyMat4) (t1Scaled : PolyVec4) :
    (outs : List SimAttemptOutcome) → (Fin outs.length → SealedAttemptPads) →
    List SealedSignAttemptView
  | [], _ => []
  | out :: rest, padFn =>
    thresholdMlDsaAttemptSimulator sampleInBall A t1Scaled out (padFn ⟨0, Nat.zero_lt_succ _⟩) ::
    thresholdMlDsaTraceSimulator sampleInBall A t1Scaled rest
      (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

def sealedTraceOutcomes
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 : PolyVec4) (mu : List UInt8)
    (steps : List SealedAttemptStepSpec) : List SimAttemptOutcome :=
  steps.map (fun stp => sealedAttemptPublicOutcome chalHash sampleInBall A s1 s2 stp.y mu stp.attempt)

private def splitPadsEquiv (n : Nat) :
    SimpleEquiv (Fin (n + 1) → SealedAttemptPads)
      (SealedAttemptPads × (Fin n → SealedAttemptPads)) where
  toFun f := (f ⟨0, Nat.zero_lt_succ _⟩, fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by funext j; refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
  right_inv := fun ⟨_, _⟩ => rfl

private def consPadEquiv {n m : Nat}
    (bijHead : SimpleEquiv SealedAttemptPads SealedAttemptPads)
    (bijRest : SimpleEquiv (Fin n → SealedAttemptPads) (Fin m → SealedAttemptPads)) :
    SimpleEquiv (Fin (n + 1) → SealedAttemptPads) (Fin (m + 1) → SealedAttemptPads) :=
  SimpleEquiv.trans (splitPadsEquiv n)
    (SimpleEquiv.trans (SimpleEquiv.prodCongr bijHead bijRest)
      (SimpleEquiv.symm (splitPadsEquiv m)))

private theorem traceSim_cons
    (sampleInBall : List UInt8 → Poly256) (A : PolyMat4) (t1Scaled : PolyVec4)
    (out : SimAttemptOutcome) (outsRest : List SimAttemptOutcome) {n : Nat}
    (bijHead : SimpleEquiv SealedAttemptPads SealedAttemptPads)
    (bijRest : SimpleEquiv (Fin n → SealedAttemptPads) (Fin outsRest.length → SealedAttemptPads))
    (padFn : Fin (n + 1) → SealedAttemptPads) :
    thresholdMlDsaTraceSimulator sampleInBall A t1Scaled (out :: outsRest)
      ((consPadEquiv bijHead bijRest).toFun padFn) =
    thresholdMlDsaAttemptSimulator sampleInBall A t1Scaled out
      (bijHead.toFun (padFn ⟨0, Nat.zero_lt_succ n⟩)) ::
    thresholdMlDsaTraceSimulator sampleInBall A t1Scaled outsRest
      (bijRest.toFun (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) := rfl

private theorem qsum_sim_eq_of_equiv {α β V : Type} {M : Nat}
    (bij : SimpleEquiv α β) (realFn : α → V) (simFn : β → V)
    (hSim : ∀ x, simFn (bij.toFun x) = realFn x)
    (enumA : SimpleEquiv (Fin M) α) (enumB : SimpleEquiv (Fin M) β)
    (D : V → Bool) :
    qsum M (fun m => (D (realFn (enumA.toFun m))).toNat) =
    qsum M (fun m => (D (simFn (enumB.toFun m))).toNat) := by
  let perm : Fin M → Fin M := fun m => enumB.invFun (bij.toFun (enumA.toFun m))
  let permInv : Fin M → Fin M := fun m => enumA.invFun (bij.invFun (enumB.toFun m))
  have hL : ∀ m, permInv (perm m) = m := fun m => by
    dsimp only [perm, permInv]; rw [enumB.right_inv, bij.left_inv, enumA.left_inv]
  have hR : ∀ m, perm (permInv m) = m := fun m => by
    dsimp only [perm, permInv]; rw [enumA.right_inv, bij.right_inv, enumB.left_inv]
  have hCong : ∀ m : Fin M,
      (D (realFn (enumA.toFun m))).toNat = (D (simFn (enumB.toFun (perm m)))).toNat := by
    intro m; dsimp only [perm]; rw [enumB.right_inv, hSim]
  rw [qsum_congr hCong]
  exact qsum_perm_invariant perm permInv hL hR (fun m => (D (simFn (enumB.toFun m))).toNat)

/-- **Abort-Transcript Zero-Knowledge Simulation Theorem (`threshold_mldsa_abort_transcript_zk`)**:
    Across any `R`-attempt signing trace where rejected attempts carry nonzero `failTag`, an
    explicit `0-Classical` pad bijection maps `realSealedSignTrace` to `thresholdMlDsaTraceSimulator`
    given public `(A, t1Scaled)` and the complete `SimAttemptOutcome` list (`none` on abort).
    This is a conditional view theorem. `outs` below is computed from the real secrets and
    masks; neither its distribution nor the number of attempts is simulated by this result.
    All algebraic view types here are the four-lane ML-DSA-44 model. -/
theorem threshold_mldsa_abort_transcript_zk
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 : PolyVec4) (mu : List UInt8)
    (steps : List SealedAttemptStepSpec)
    (hFail : ∀ stp ∈ steps, stp.failTag ≠ Fq204.zero) :
    let t1Scaled := power2RoundHighVec4 (addVec4 (matVecMul4 A s1) s2)
    let outs := sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu steps
    ∃ (_hLen : outs.length = steps.length)
      (padBij : SimpleEquiv (Fin steps.length → SealedAttemptPads)
                            (Fin outs.length → SealedAttemptPads)),
      (∀ padFn,
        thresholdMlDsaTraceSimulator sampleInBall A t1Scaled outs (padBij.toFun padFn) =
          realSealedSignTrace chalHash sampleInBall A s1 s2 mu steps padFn) ∧
      (∀ {M : Nat} (enum : SimpleEquiv (Fin M) (Fin steps.length → SealedAttemptPads))
         (enumOut : SimpleEquiv (Fin M) (Fin outs.length → SealedAttemptPads))
         (D : List SealedSignAttemptView → Bool),
        qsum M (fun m =>
          (D (realSealedSignTrace chalHash sampleInBall A s1 s2 mu steps (enum.toFun m))).toNat) =
        qsum M (fun m =>
          (D (thresholdMlDsaTraceSimulator sampleInBall A t1Scaled outs (enumOut.toFun m))).toNat)) := by
  induction steps with
  | nil => exact ⟨rfl, SimpleEquiv.refl _, (fun _ => rfl), fun _ _ _ => rfl⟩
  | cons stp rest ih =>
    have hHeadFail : stp.failTag ≠ Fq204.zero := hFail stp (.head rest)
    obtain ⟨_, bijRest, hEqRest, _⟩ := ih (fun s hs => hFail s (.tail stp hs))
    have hLenCons : (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu (stp :: rest)).length =
        (stp :: rest).length := List.length_map _
    have hPointwise : ∀ padFn : Fin (rest.length + 1) → SealedAttemptPads,
        thresholdMlDsaTraceSimulator sampleInBall A
          (power2RoundHighVec4 (addVec4 (matVecMul4 A s1) s2))
          (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu (stp :: rest))
          ((consPadEquiv (sealedStepPadEquiv chalHash sampleInBall A s1 s2 stp.y mu
              stp.keccakTraceBits stp.failTag hHeadFail) bijRest).toFun padFn) =
        realSealedSignTrace chalHash sampleInBall A s1 s2 mu (stp :: rest) padFn := by
      intro padFn
      have hHd := sealedAttempt_sim_eq_real chalHash sampleInBall A s1 s2 stp.y mu stp.attempt
        stp.keccakTraceBits stp.failTag hHeadFail (padFn ⟨0, Nat.zero_lt_succ _⟩)
      have hTl := hEqRest (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      exact (traceSim_cons sampleInBall A (power2RoundHighVec4 (addVec4 (matVecMul4 A s1) s2))
        (sealedAttemptPublicOutcome chalHash sampleInBall A s1 s2 stp.y mu stp.attempt)
        (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu rest)
        (sealedStepPadEquiv chalHash sampleInBall A s1 s2 stp.y mu
          stp.keccakTraceBits stp.failTag hHeadFail)
        bijRest padFn).trans (by dsimp only [realSealedSignTrace]; rw [hHd, hTl])
    exact ⟨hLenCons,
      consPadEquiv (sealedStepPadEquiv chalHash sampleInBall A s1 s2 stp.y mu
        stp.keccakTraceBits stp.failTag hHeadFail) bijRest,
      hPointwise,
      fun enum enumOut D => qsum_sim_eq_of_equiv _ _ _ hPointwise enum enumOut D⟩

def maskCoordAt (gamma1 : Nat) (idx : Fin (2 * gamma1 - 1)) : Int :=
  (idx.val : Int) - ((gamma1 : Int) - 1)

def inOpenNormBox (B : Nat) (z : Int) : Bool :=
  decide (-((B : Int)) < z ∧ z < (B : Int))

/-- **Plateau Shift-Invariance (`fips204_z_plateau_shift_invariant`)**:
    Over `y ∈ [-(γ₁ - 1), γ₁ - 1]`, for every `cs1 ∈ [-β, β]` and `|zStar| < γ₁ - β`, exactly
    `1` mask index satisfies `y + cs1 = zStar`, independent of `cs1`. -/
theorem fips204_z_plateau_shift_invariant
    (gamma1 beta : Nat) (hLt : beta < gamma1) (cs1 zStar : Int)
    (hCs1 : -((beta : Int)) ≤ cs1 ∧ cs1 ≤ (beta : Int))
    (hOpen : inOpenNormBox (gamma1 - beta) zStar = true) :
    qsum (2 * gamma1 - 1) (fun idx =>
      if maskCoordAt gamma1 idx + cs1 = zStar then 1 else 0) = 1 := by
  unfold inOpenNormBox at hOpen
  have hZ := of_decide_eq_true hOpen
  have hSub : ((gamma1 - beta : Nat) : Int) = (gamma1 : Int) - (beta : Int) :=
    Int.ofNat_sub (Nat.le_of_lt hLt)
  rw [hSub] at hZ
  let xInt : Int := zStar - cs1 + ((gamma1 : Int) - 1)
  have hx0 : 0 ≤ xInt := by dsimp only [xInt]; omega
  have hxHi : xInt < 2 * (gamma1 : Int) - 1 := by dsimp only [xInt]; omega
  let kNat : Nat := xInt.toNat
  have hkCast : (kNat : Int) = xInt := Int.toNat_of_nonneg hx0
  have hkLt : kNat < 2 * gamma1 - 1 := by omega
  let targetIdx : Fin (2 * gamma1 - 1) := ⟨kNat, hkLt⟩
  have hiff : ∀ idx : Fin (2 * gamma1 - 1),
      (if maskCoordAt gamma1 idx + cs1 = zStar then 1 else 0) =
      (if idx = targetIdx then 1 else 0) := by
    intro idx; unfold maskCoordAt
    if hEq : idx = targetIdx then
      rw [ite_true hEq, hEq]
      have hMatch : (targetIdx.val : Int) - ((gamma1 : Int) - 1) + cs1 = zStar := by
        dsimp only [targetIdx]; rw [hkCast]; dsimp only [xInt]; omega
      rw [ite_true hMatch]
    else
      rw [ite_false hEq]
      have hValNe : idx.val ≠ kNat := fun hv => hEq (Fin.ext hv)
      have hNeZ : (idx.val : Int) - ((gamma1 : Int) - 1) + cs1 ≠ zStar := by
        intro hz; apply hValNe
        have hCastEq : (idx.val : Int) = (kNat : Int) := by
          rw [hkCast]; dsimp only [xInt]; omega
        exact Int.ofNat.inj hCastEq
      rw [ite_false hNeZ]
  rw [qsum_congr hiff]
  exact qsum_eq_indicator (2 * gamma1 - 1) targetIdx

def unsealedEarlyW1AbortHit (cs1 : Int) (idx : Fin 9) : Bool :=
  let y := maskCoordAt 5 idx
  decide ((y + 4) / 2 = 3) && !inOpenNormBox 3 (y + cs1)

def irwinHall2HitCount (cs1 zTarget : Int) : Nat :=
  qsum 5 (fun i => qsum 5 (fun j =>
    if ((i.val : Int) - 2) + ((j.val : Int) - 2) + cs1 = zTarget then 1 else 0))

/-- **`#tooth` (`tooth_unsealed_w1_or_irwin_hall_abort_leaks_secret`)**:
    Early `(w₁, reject)` opening (`unsealedEarlyW1AbortHit`) and unflooded 2-party Irwin-Hall
    mask sums (`irwinHall2HitCount`) both vary with secret `cs₁ ∈ {0, 1}`, whereas the sealed
    abort simulator `thresholdMlDsaTraceSimulator` opens `released = none` independent of `(s₁, s₂)`. -/
theorem tooth_unsealed_w1_or_irwin_hall_abort_leaks_secret :
    ∃ pads : SealedAttemptPads,
      qsum 9 (fun idx => (unsealedEarlyW1AbortHit 0 idx).toNat) ≠
        qsum 9 (fun idx => (unsealedEarlyW1AbortHit 1 idx).toNat) ∧
      irwinHall2HitCount 0 0 ≠ irwinHall2HitCount 1 0 ∧
      (thresholdMlDsaTraceSimulator (fun _ => PolyTree.zero 8) idMat4 rssZeroVec4
        [none] (fun _ => pads)).map SealedSignAttemptView.released = [none] :=
  ⟨⟨rssZeroVec4, rssZeroVec4, rssZeroVec4, 0#256, ext6Zero⟩, by decide, by decide, rfl⟩

theorem fips204_z_plateau_witness :
    ∃ (gamma1 beta : Nat) (cs1 zStar : Int),
      beta < gamma1 ∧
      (-((beta : Int)) ≤ cs1 ∧ cs1 ≤ (beta : Int)) ∧
      inOpenNormBox (gamma1 - beta) zStar = true :=
  ⟨5, 2, 1, 0, by decide, ⟨by decide, by decide⟩, by decide⟩

theorem threshold_mldsa_abort_zk_witness :
    ∃ (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
      (sampleInBall : List UInt8 → Poly256)
      (A : PolyMat4) (s1 s2 : PolyVec4) (mu : List UInt8)
      (steps : List SealedAttemptStepSpec),
      (∀ stp ∈ steps, stp.failTag ≠ Fq204.zero) ∧
      (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu steps).length = steps.length := by
  refine ⟨(fun _ _ => []), (fun _ => PolyTree.zero 8), idMat4, rssZeroVec4, rssZeroVec4, [],
    [{ y := rssZeroVec4, attempt := 0, keccakTraceBits := 0#256, failTag := Fq204.one }],
    ?_, List.length_map _⟩
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hNil
  · decide
  · cases hNil

/-! ## §3. 3-Party `(2, 3)` RSS Multiplication + Sacrifice Refinement & `C(n, t - 1)` PRSS Hybrid -/

/-- Category-3 deployment profile. ML-DSA-44 and RSS3 below remain explicit
compatibility instances, rather than the committee or level of the general API. -/
def deployedThresholdMlDsaProfile : MlDsaLevelSpec := mlDsa65Spec

structure MlDsaThresholdQuorum (t n : Nat) where
  positive : 0 < t
  threshold_le : t ≤ n
  parties : List (Fin n)
  distinct : parties.Nodup
  enough : t ≤ parties.length
  sharing : ShamirQuorum Fq204 t
  points_match : sharing.pts.length = parties.length
  weights_match : sharing.lambdas.length = parties.length

/-- Reconstruction is tied to actual quorum evaluations of a degree-<t
polynomial over the ML-DSA field, for arbitrary t and n. -/
theorem mldsa_threshold_quorum_reconstruct {t n : Nat}
    (q : MlDsaThresholdQuorum t n) (coeffs : List Fq204) (hDegree : coeffs.length ≤ t) :
    ringDot q.sharing.lambdas (q.sharing.pts.map (RoundPoly.evalCoeffs coeffs)) =
      RoundPoly.evalCoeffs coeffs CommRingOps.zero :=
  lagrangeAtZero_evalCoeffs q.sharing.lambdas q.sharing.pts coeffs t hDegree
    q.sharing.sum_one (fun d hd ht => by
      simpa only [ringDot_eq, ringPow_eq] using q.sharing.kills_higher d hd ht)

theorem deployedThresholdMlDsaProfile_category3 :
    deployedThresholdMlDsaProfile.k = 6 ∧ deployedThresholdMlDsaProfile.ell = 5 ∧
    deployedThresholdMlDsaProfile.tau = 49 ∧ deployedThresholdMlDsaProfile.beta = 196 ∧
    deployedThresholdMlDsaProfile.gamma1 = 524288 ∧
    mlDsaLevelWellFormed deployedThresholdMlDsaProfile = true := by decide

#verify_constructive mldsa_threshold_quorum_reconstruct deployedThresholdMlDsaProfile_category3

structure Rss3Share where
  s0 : Fq204
  s1 : Fq204
  s2 : Fq204
  deriving DecidableEq, Repr

def rss3Recon (x : Rss3Share) : Fq204 :=
  Fq204.add (Fq204.add x.s0 x.s1) x.s2

def rss3MulStep (x y : Rss3Share) (r0 r1 : Fq204) (delta : Fq204) : Rss3Share :=
  let u0 := Fq204.add (Fq204.add (Fq204.mul x.s1 y.s1) (Fq204.mul x.s1 y.s2)) (Fq204.mul x.s2 y.s1)
  let u1 := Fq204.add (Fq204.add (Fq204.mul x.s2 y.s2) (Fq204.mul x.s2 y.s0)) (Fq204.mul x.s0 y.s2)
  let u2 := Fq204.add (Fq204.add (Fq204.mul x.s0 y.s0) (Fq204.mul x.s0 y.s1)) (Fq204.mul x.s1 y.s0)
  { s0 := Fq204.add (Fq204.add u0 r0) delta
    s1 := Fq204.add u1 r1
    s2 := Fq204.add u2 (Fq204.neg (Fq204.add r0 r1)) }

theorem rss3MulStep_recon (x y : Rss3Share) (r0 r1 delta : Fq204) :
    rss3Recon (rss3MulStep x y r0 r1 delta) =
      Fq204.add (Fq204.mul (rss3Recon x) (rss3Recon y)) delta := by
  unfold rss3Recon rss3MulStep; dsimp only
  rw [← Fq204.ofInt_nat x.s0, ← Fq204.ofInt_nat x.s1, ← Fq204.ofInt_nat x.s2,
      ← Fq204.ofInt_nat y.s0, ← Fq204.ofInt_nat y.s1, ← Fq204.ofInt_nat y.s2,
      ← Fq204.ofInt_nat r0, ← Fq204.ofInt_nat r1, ← Fq204.ofInt_nat delta]
  simp only [Fq204.ofInt_add, Fq204.ofInt_mul, Fq204.ofInt_neg]
  congr 1; simp only [Int.add_mul, Int.mul_add]; omega

def rss3ToSacGate (x y : Rss3Share) (r0 r1 deltaZ : Fq204)
    (a : Ext6Fq204) (b : Rss3Share) (deltaC : Ext6Fq204) : SacGate204 :=
  { x := rss3Recon x, y := rss3Recon y, z := rss3Recon (rss3MulStep x y r0 r1 deltaZ),
    a := a, b := rss3Recon b, c := ext6Add (ext6Scale a (rss3Recon b)) deltaC }

theorem rss3ToSacGate_error_eq_delta (x y : Rss3Share) (r0 r1 deltaZ : Fq204)
    (a : Ext6Fq204) (b : Rss3Share) (deltaC : Ext6Fq204) :
    sacGateError204 (rss3ToSacGate x y r0 r1 deltaZ a b deltaC) = deltaZ := by
  rw [sacGateError204_eq]
  unfold rss3ToSacGate
  dsimp only
  rw [rss3MulStep_recon,
      ← Fq204.ofInt_nat (Fq204.mul (rss3Recon x) (rss3Recon y)), ← Fq204.ofInt_nat deltaZ]
  simp only [Fq204.ofInt_add, Fq204.ofInt_sub]
  have hCancel :
      (((Fq204.mul (rss3Recon x) (rss3Recon y)).val : Int) + (deltaZ.val : Int)) -
        ((Fq204.mul (rss3Recon x) (rss3Recon y)).val : Int) = (deltaZ.val : Int) := by omega
  rw [hCancel, Fq204.ofInt_nat]

def sacAcceptRepeated (chis : List Ext6Fq204) (g : SacGate204) : Bool :=
  chis.all (fun chi => sacAccept204 chi g)

/-- **Repeated Sacrifice Cheating Rejection (`rss3_repeated_sacrifice_pq256`)**:
    Any nonzero `deltaZ ≠ 0` survives `sacAcceptRepeated chis` only if every `chi ∈ chis` equals
    `sacBadChallenge204 g` (`≤ 1 / q` per base challenge; `2^256 < mldsaQ^12`). -/
theorem rss3_repeated_sacrifice_pq256
    (x y : Rss3Share) (r0 r1 deltaZ : Fq204)
    (a : Ext6Fq204) (b : Rss3Share) (deltaC : Ext6Fq204)
    (chis : List Ext6Fq204) (hCheat : deltaZ ≠ Fq204.zero) :
    (sacAcceptRepeated chis (rss3ToSacGate x y r0 r1 deltaZ a b deltaC) = true →
      ∀ chi ∈ chis, chi = sacBadChallenge204 (rss3ToSacGate x y r0 r1 deltaZ a b deltaC)) ∧
    2 ^ 256 < mldsaQ ^ 12 := by
  refine ⟨?_, by decide⟩
  intro hAll chi hMem
  unfold sacAcceptRepeated at hAll; rw [List.all_eq_true] at hAll
  rcases sacAccept204_sound (hAll chi hMem) with hEq | hBad
  · have hErr0 : sacGateError204 (rss3ToSacGate x y r0 r1 deltaZ a b deltaC) = Fq204.zero := by
      rw [sacGateError204_eq, hEq, Fq204.sub_eq_add_neg, Fq204.add_right_neg]
    rw [rss3ToSacGate_error_eq_delta] at hErr0
    exact False.elim (hCheat hErr0)
  · exact hBad

def runRssSacrificedTrace
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    RssMlDsaSignerState →
    List (RssMlDsaAttemptInput × Ext6Fq204 × RssSacrificeTranscript204) →
    RssMlDsaSignerState × List (StepOutcome RssMlDsaSignerState
      (RssSignPublicAbortView × Option ThresholdSignSig) RssPreOpenAbortReason)
  | st, [] => (st, [])
  | st, (inp, chi, T) :: rest =>
    let out := rssSacrificedSignStep chalHash sampleInBall st inp chi T
    let stNext := out.nextState
    let tail := runRssSacrificedTrace chalHash sampleInBall stNext rest
    (tail.1, out :: tail.2)

theorem rss_distributed_trace_refines_sacrificedSignStep
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    ∀ (st : RssMlDsaSignerState)
      (tr : List (RssMlDsaAttemptInput × Ext6Fq204 × RssSacrificeTranscript204)),
      st.nextAttempt ≤ (runRssSacrificedTrace chalHash sampleInBall st tr).1.nextAttempt ∧
      (∀ turn ∈ tr, ∀ stCur : RssMlDsaSignerState,
        rssSacrificedSignStep chalHash sampleInBall stCur turn.1 turn.2.1 turn.2.2 =
          rssThresholdSignStep chalHash sampleInBall stCur turn.1 ∨
        (∃ st', rssSacrificedSignStep chalHash sampleInBall stCur turn.1 turn.2.1 turn.2.2 =
          .err st' .mpcSacrificeFailed) ∨
        turn.2.1 ∈ rssSacrificeBadChallenges204 turn.2.2)
  | st, [] => ⟨Nat.le_refl _, fun _ h => nomatch h⟩
  | st, (inp, chi, T) :: rest => by
    let out := rssSacrificedSignStep chalHash sampleInBall st inp chi T
    let stNext := out.nextState
    have hStepMono : st.nextAttempt ≤ stNext.nextAttempt := by
      dsimp only [stNext, out]; unfold rssSacrificedSignStep
      cases decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
      | false => exact Nat.le_refl _
      | true =>
        cases rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
        | false => change st.nextAttempt ≤ st.nextAttempt + 1; omega
        | true =>
          dsimp only
          rw [rssSignCore_nextState]
          dsimp only; omega
    obtain ⟨hTailMono, hTailRef⟩ :=
      rss_distributed_trace_refines_sacrificedSignStep chalHash sampleInBall stNext rest
    refine ⟨Nat.le_trans hStepMono hTailMono, ?_⟩
    intro turn hMem stCur
    rcases List.mem_cons.mp hMem with rfl | hInRest
    · dsimp only
      cases hv : rssSacrificedProductsValid chalHash sampleInBall stCur inp chi T with
      | true =>
        rcases rssSacrificedSignStep_refines chalHash sampleInBall stCur inp chi T hv with hEq | hBad
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hBad)
      | false =>
        unfold rssSacrificedSignStep
        cases hg : decide (inp.epoch = stCur.epoch ∧ inp.attempt = stCur.nextAttempt) with
        | false => left; unfold rssThresholdSignStep; rw [hg]
        | true => right; left; rw [hv]; exact ⟨{ stCur with nextAttempt := stCur.nextAttempt + 1 }, rfl⟩
    · exact hTailRef turn hInRest stCur

theorem rss_prss_choose_hybrid {O : Type} {N : Nat} (real ideal : Fin N → O)
    (n t : Nat) (D : List O → Bool) (ε : Nat) (hPRF : PrssSingleKeyBound real ideal D ε) :
    let numKeys := binomRec n (t - 1)
    prssGap (prssRealHits real numKeys D) (prssIdealHits ideal numKeys D) ≤
      numKeys * (N ^ (numKeys - 1) * ε) :=
  prss_multi_key_hybrid real ideal (binomRec n (t - 1)) D ε hPRF

theorem rss_deployed_quorum_subset_counts :
    binomRec 3 (2 - 1) = 3 ∧ binomRec 5 (2 - 1) = 5 ∧ binomRec 5 (3 - 1) = 10 := by decide

#verify_constructive mlDsa_all_three_levels_wellFormed mlDsa_challenge_entropy_bounds
  mlDsa65_87_highBits_bounds eta4SampleNibble_bijective_on_range rss3MulStep_recon
  rss_distributed_trace_refines_sacrificedSignStep rss_prss_choose_hybrid
#tooth_pair mlDsa_all_three_levels_wellFormed vs tooth_mlDsaLevelWellFormed_bad_beta
#tooth_pair threshold_mldsa_abort_transcript_zk vs tooth_unsealed_w1_or_irwin_hall_abort_leaks_secret
#verify_inhabited threshold_mldsa_abort_transcript_zk threshold_mldsa_abort_zk_witness
#tooth_pair fips204_z_plateau_shift_invariant vs tooth_unsealed_w1_or_irwin_hall_abort_leaks_secret
#verify_inhabited fips204_z_plateau_shift_invariant fips204_z_plateau_witness


/-! ## §4. Asymmetric `[-γ₁ + 1, γ₁]` Mask Boundary & Rectangular `ML-DSA-44/65/87` Abort-Transcript ZK -/

/-- Exact NIST FIPS 204 `ExpandMask` coordinate mapping (`Algorithm 34`, `BitUnpack(v, γ₁ - 1, γ₁)`):
    maps a uniform integer `u ∈ [0, 2γ₁)` to `y = γ₁ - u ∈ [-γ₁ + 1, γ₁]` (`2γ₁` support points). -/
def fips204ExpandMaskCoord (gamma1 : Nat) (u : Fin (2 * gamma1)) : Int :=
  (gamma1 : Int) - (u.val : Int)

theorem fips204ExpandMaskCoord_range (gamma1 : Nat) (hPos : 0 < gamma1) :
    (∀ u : Fin (2 * gamma1),
      -((gamma1 : Int)) + 1 ≤ fips204ExpandMaskCoord gamma1 u ∧
      fips204ExpandMaskCoord gamma1 u ≤ (gamma1 : Int)) ∧
    fips204ExpandMaskCoord gamma1 ⟨0, by omega⟩ = (gamma1 : Int) ∧
    fips204ExpandMaskCoord gamma1 ⟨2 * gamma1 - 1, by omega⟩ = -((gamma1 : Int)) + 1 := by
  refine ⟨fun u => ?_, ?_, ?_⟩
  · unfold fips204ExpandMaskCoord; have hu := u.isLt; constructor <;> omega
  · unfold fips204ExpandMaskCoord; dsimp only; omega
  · unfold fips204ExpandMaskCoord; dsimp only; omega

/-- **Exact FIPS 204 Asymmetric `2γ₁` Plateau Shift-Invariance
    (`fips204_asymmetric_2gamma1_plateau_shift_invariant`)**:
    Over the true FIPS 204 `ExpandMask` support `y ∈ [-γ₁ + 1, γ₁]` (`2γ₁` points), for every
    secret shift `cs1 ∈ [-β, β]` and every open-box target `zStar` with `|zStar| < γ₁ - β`,
    exactly `1` mask preimage `u ∈ Fin (2γ₁)` satisfies `fips204ExpandMaskCoord gamma1 u + cs1 = zStar`,
    completely independent of `cs1`. -/
theorem fips204_asymmetric_2gamma1_plateau_shift_invariant
    (gamma1 beta : Nat) (hLt : beta < gamma1) (cs1 zStar : Int)
    (hCs1 : -((beta : Int)) ≤ cs1 ∧ cs1 ≤ (beta : Int))
    (hOpen : inOpenNormBox (gamma1 - beta) zStar = true) :
    qsum (2 * gamma1) (fun u =>
      if fips204ExpandMaskCoord gamma1 u + cs1 = zStar then 1 else 0) = 1 := by
  unfold inOpenNormBox at hOpen
  have hZ := of_decide_eq_true hOpen
  have hSub : ((gamma1 - beta : Nat) : Int) = (gamma1 : Int) - (beta : Int) :=
    Int.ofNat_sub (Nat.le_of_lt hLt)
  rw [hSub] at hZ
  let uInt : Int := (gamma1 : Int) + cs1 - zStar
  have hu0 : 0 ≤ uInt := by dsimp only [uInt]; omega
  have huHi : uInt < 2 * (gamma1 : Int) := by dsimp only [uInt]; omega
  let uNat : Nat := uInt.toNat
  have huCast : (uNat : Int) = uInt := Int.toNat_of_nonneg hu0
  have huLt : uNat < 2 * gamma1 := by omega
  let targetU : Fin (2 * gamma1) := ⟨uNat, huLt⟩
  have hiff : ∀ u : Fin (2 * gamma1),
      (if fips204ExpandMaskCoord gamma1 u + cs1 = zStar then 1 else 0) =
      (if u = targetU then 1 else 0) := by
    intro u; unfold fips204ExpandMaskCoord
    if hEq : u = targetU then
      rw [ite_true hEq, hEq]
      have hMatch : (gamma1 : Int) - (targetU.val : Int) + cs1 = zStar := by
        dsimp only [targetU]; rw [huCast]; dsimp only [uInt]; omega
      rw [ite_true hMatch]
    else
      rw [ite_false hEq]
      have hValNe : u.val ≠ uNat := fun hv => hEq (Fin.ext hv)
      have hNeZ : (gamma1 : Int) - (u.val : Int) + cs1 ≠ zStar := by
        intro hz; apply hValNe
        have hCastEq : (u.val : Int) = (uNat : Int) := by
          rw [huCast]; dsimp only [uInt]; omega
        exact Int.ofNat.inj hCastEq
      rw [ite_false hNeZ]
  rw [qsum_congr hiff]
  exact qsum_eq_indicator (2 * gamma1) targetU

private theorem qsum_eq_zero_of_all_zero :
    ∀ (n : Nat) (f : Fin n → Nat), (∀ i : Fin n, f i = 0) → qsum n f = 0
  | 0, _, _ => rfl
  | n + 1, f, h => by
    unfold qsum
    rw [h ⟨0, Nat.zero_lt_succ n⟩,
        qsum_eq_zero_of_all_zero n _ (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

/-- **`#tooth` (`tooth_closed_box_le_breaks_asymmetric_2gamma1_plateau`)**:
    Relaxing FIPS 204's strict open-box check `|z| < γ₁ - β` to the closed bound `|z| ≤ γ₁ - β`
    leaks `c · s₁` on the asymmetric `ExpandMask` support `[-γ₁ + 1, γ₁]`: at the negative closed
    boundary `zNeg = -(γ₁ - β)` (`|zNeg| = γ₁ - β`), secret shift `cs1 = +β` requires `y = -γ₁`
    which is absent from `[-γ₁ + 1, γ₁]` (`0` preimages), whereas `cs1 = 0` has `1` preimage. -/
theorem tooth_closed_box_le_breaks_asymmetric_2gamma1_plateau
    (gamma1 beta : Nat) (hBetaPos : 0 < beta) (hLt : beta < gamma1) :
    qsum (2 * gamma1) (fun u =>
      if fips204ExpandMaskCoord gamma1 u + (beta : Int) = -((gamma1 - beta : Nat) : Int) then 1 else 0) ≠
    qsum (2 * gamma1) (fun u =>
      if fips204ExpandMaskCoord gamma1 u + 0 = -((gamma1 - beta : Nat) : Int) then 1 else 0) := by
  let zNeg : Int := -((gamma1 - beta : Nat) : Int)
  change qsum (2 * gamma1) (fun u =>
      if fips204ExpandMaskCoord gamma1 u + (beta : Int) = zNeg then 1 else 0) ≠
    qsum (2 * gamma1) (fun u =>
      if fips204ExpandMaskCoord gamma1 u + 0 = zNeg then 1 else 0)
  have hSub : ((gamma1 - beta : Nat) : Int) = (gamma1 : Int) - (beta : Int) :=
    Int.ofNat_sub (Nat.le_of_lt hLt)
  have hZeroHits : qsum (2 * gamma1) (fun u =>
      if fips204ExpandMaskCoord gamma1 u + (beta : Int) = zNeg then 1 else 0) = 0 := by
    apply qsum_eq_zero_of_all_zero
    intro u; unfold fips204ExpandMaskCoord
    have hu := u.isLt
    have hNe : (gamma1 : Int) - (u.val : Int) + (beta : Int) ≠ zNeg := by
      dsimp only [zNeg]; rw [hSub]; omega
    exact ite_false hNe 1 0
  have hOneHit : qsum (2 * gamma1) (fun u =>
      if fips204ExpandMaskCoord gamma1 u + 0 = zNeg then 1 else 0) = 1 := by
    let uNat : Nat := 2 * gamma1 - beta
    have huLt : uNat < 2 * gamma1 := by dsimp only [uNat]; omega
    let targetU : Fin (2 * gamma1) := ⟨uNat, huLt⟩
    have hiff : ∀ u : Fin (2 * gamma1),
        (if fips204ExpandMaskCoord gamma1 u + 0 = zNeg then 1 else 0) =
        (if u = targetU then 1 else 0) := by
      intro u; unfold fips204ExpandMaskCoord
      if hEq : u = targetU then
        rw [ite_true hEq, hEq]
        have hMatch : (gamma1 : Int) - (targetU.val : Int) + 0 = zNeg := by
          dsimp only [targetU, uNat, zNeg]; rw [hSub]; omega
        rw [ite_true hMatch]
      else
        rw [ite_false hEq]
        have hValNe : u.val ≠ uNat := fun hv => hEq (Fin.ext hv)
        have hNe : (gamma1 : Int) - (u.val : Int) + 0 ≠ zNeg := by
          dsimp only [zNeg]; rw [hSub]; intro hz; apply hValNe; dsimp only [uNat]; omega
        rw [ite_false hNe]
    rw [qsum_congr hiff]
    exact qsum_eq_indicator (2 * gamma1) targetU
  rw [hZeroHits, hOneHit]
  decide

theorem fips204_asymmetric_2gamma1_plateau_witness :
    ∃ (gamma1 beta : Nat) (cs1 zStar : Int),
      beta < gamma1 ∧
      (-((beta : Int)) ≤ cs1 ∧ cs1 ≤ (beta : Int)) ∧
      inOpenNormBox (gamma1 - beta) zStar = true :=
  ⟨524288, 196, 196, -524091, by decide, ⟨by decide, by decide⟩, by decide⟩

/-- Exact NIST FIPS 204 `Decompose(r)` (`Algorithm 36`) for `ML-DSA-65` and `ML-DSA-87`
    (`γ₂ = (q - 1) / 32 = 261888, α = 2γ₂ = 523776, m = 16`). -/
def decompose32 (r : Fq204) : Nat × Int :=
  let rem : Nat := r.val % 523776
  let r0p : Int := if 261888 < rem then (rem : Int) - 523776 else (rem : Int)
  if (r.val : Int) - r0p = 8380416 then
    (0, r0p - 1)
  else
    (((r.val : Int) - r0p).toNat / 523776, r0p)

def mldsaHighBits32 (r : Fq204) : Nat := (decompose32 r).1
def mldsaLowBits32 (r : Fq204) : Int := (decompose32 r).2

theorem mldsaHighBits32_eq_fips204HighBits32 (r : Fq204) :
    mldsaHighBits32 r = fips204HighBits32 r := by
  have hr := r.isLt
  unfold mldsaHighBits32 decompose32 fips204HighBits32 mldsaQ at *
  dsimp only
  split <;> split <;> split <;> omega

theorem decompose32_reconstruct (r : Fq204) :
    mldsaHighBits32 r < 16 ∧
    -261888 ≤ mldsaLowBits32 r ∧ mldsaLowBits32 r ≤ 261888 ∧
    (mldsaHighBits32 r ≠ 0 → -261888 < mldsaLowBits32 r) ∧
    Fq204.ofInt ((mldsaHighBits32 r : Int) * 523776 + mldsaLowBits32 r) = r := by
  have hr := r.isLt
  have hCore :
      mldsaHighBits32 r < 16 ∧
      -261888 ≤ mldsaLowBits32 r ∧ mldsaLowBits32 r ≤ 261888 ∧
      (mldsaHighBits32 r ≠ 0 → -261888 < mldsaLowBits32 r) ∧
      (((mldsaHighBits32 r : Int) * 523776 + mldsaLowBits32 r = (r.val : Int)) ∨
       ((mldsaHighBits32 r : Int) * 523776 + mldsaLowBits32 r = (r.val : Int) - 8380417)) := by
    unfold mldsaHighBits32 mldsaLowBits32 decompose32
    unfold mldsaQ at hr
    dsimp only
    split <;> split <;> dsimp only <;> (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega)
  refine ⟨hCore.1, hCore.2.1, hCore.2.2.1, hCore.2.2.2.1, ?_⟩
  rcases hCore.2.2.2.2 with hExact | hWrap
  · rw [hExact, Fq204.ofInt_nat]
  · rw [hWrap]
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val]; unfold mldsaQ at hr ⊢
    rw [← Int.add_emod_right _ ((8380417 : Nat) : Int)]
    have hCancel : (r.val : Int) - 8380417 + ((8380417 : Nat) : Int) = (r.val : Int) := by omega
    rw [hCancel]
    exact Int.emod_eq_of_lt (by omega) (by omega)

theorem decompose32_ofInt_interior {u1 : Nat} {u0 : Int}
    (hu1 : u1 < 16) (hu0Lo : -261888 < u0 ∨ (u1 = 0 ∧ u0 = -261888)) (hu0Hi : u0 ≤ 261888) :
    decompose32 (Fq204.ofInt ((u1 : Int) * 523776 + u0)) = (u1, u0) := by
  if hCorner : (u1 = 0 ∧ u0 = -261888) ∨ (u1 = 0 ∧ u0 = -1) then
    rcases hCorner with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  else
    have hu0Strict : -261888 < u0 := by
      rcases hu0Lo with h | h
      · exact h
      · exact absurd (Or.inl h) hCorner
    clear hu0Lo
    have hv : ((Fq204.ofInt ((u1 : Int) * 523776 + u0)).val : Int) =
        ((u1 : Int) * 523776 + u0) % (8380417 : Int) := Fq204.ofInt_val _
    unfold decompose32
    if hWrap : u1 = 0 ∧ u0 < 0 then
      rcases hWrap with ⟨hu1Zero, hu0Neg⟩
      subst hu1Zero
      have hu0NeM1 : u0 ≠ -1 := fun h => hCorner (Or.inr ⟨rfl, h⟩)
      clear hCorner
      have hu0LeMinus2 : u0 ≤ -2 := by omega
      simp only [Int.ofNat_zero, Int.zero_mul, Int.zero_add] at hv ⊢
      have hMod : u0 % (8380417 : Int) = 8380417 + u0 := by
        rw [← Int.add_emod_right u0 (8380417 : Int)]
        have hEq : u0 + (8380417 : Int) = 8380417 + u0 := by omega
        rw [hEq]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [hMod] at hv
      generalize (Fq204.ofInt u0).val = n at hv ⊢
      have hnDiv : n / 523776 = 15 := by omega
      have hgt : 261888 < n % 523776 := by omega
      have htop : (n : Int) - (((n % 523776 : Nat) : Int) - 523776) = 8380416 := by omega
      simp only [hgt, ↓reduceIte, htop]
      exact Prod.ext rfl (by omega)
    else
      have hNonneg : 0 ≤ (u1 : Int) * 523776 + u0 := by
        rcases Nat.eq_zero_or_pos u1 with h0 | hpos
        · have hu0nn : ¬ (u0 < 0) := fun h => hWrap ⟨h0, h⟩
          clear hWrap hCorner; omega
        · clear hWrap hCorner; omega
      clear hWrap hCorner
      have hMod : ((u1 : Int) * 523776 + u0) % (8380417 : Int) = (u1 : Int) * 523776 + u0 :=
        Int.emod_eq_of_lt hNonneg (by omega)
      rw [hMod] at hv
      generalize (Fq204.ofInt ((u1 : Int) * 523776 + u0)).val = n at hv ⊢
      dsimp only
      if hu0Pos : 0 ≤ u0 then
        have hngt : ¬ (261888 < n % 523776) := by omega
        have hntop : (n : Int) - ((n % 523776 : Nat) : Int) ≠ 8380416 := by omega
        simp only [hngt, ↓reduceIte, hntop]
        exact Prod.ext (by omega) (by omega)
      else
        have hgt : 261888 < n % 523776 := by omega
        have hntop : (n : Int) - (((n % 523776 : Nat) : Int) - 523776) ≠ 8380416 := by omega
        simp only [hgt, ↓reduceIte, hntop]
        exact Prod.ext (by omega) (by omega)

theorem centered_diff32_lt_iff_lowBits_and_highBits (r : Fq204) {w1 B : Nat}
    (hw1 : w1 < 16) (hB : B ≤ 261888) :
    Fq204.centeredAbs (Fq204.sub r (Fq204.ofNat (w1 * 523776))) < B ↔
      (mldsaLowBits32 r).natAbs < B ∧ mldsaHighBits32 r = w1 := by
  have hw1Int : Fq204.ofNat (w1 * 523776) = Fq204.ofInt ((w1 : Int) * 523776) := by
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val, Fq204.ofNat_val, Int.natCast_emod, Int.natCast_mul]
    rfl
  constructor
  · intro hAbs
    let diff := Fq204.sub r (Fq204.ofNat (w1 * 523776))
    let d := Fq204.toCenteredInt diff
    have hdAbs : d.natAbs < B := by dsimp [d]; rwa [Fq204.toCenteredInt_natAbs]
    have hrEq : r = Fq204.ofInt ((w1 : Int) * 523776 + d) := by
      calc r = Fq204.add (Fq204.ofNat (w1 * 523776)) diff := by
            dsimp [diff]
            rw [Fq204.sub_eq_add_neg, Fq204.add_comm _ (Fq204.add r _),
                Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
      _ = Fq204.add (Fq204.ofInt ((w1 : Int) * 523776)) (Fq204.ofInt d) := by
            rw [hw1Int, Fq204.ofInt_toCenteredInt]
      _ = Fq204.ofInt ((w1 : Int) * 523776 + d) := Fq204.ofInt_add _ _
    have hdec := decompose32_ofInt_interior hw1 (u0 := d) (Or.inl (by omega)) (by omega)
    rw [← hrEq] at hdec
    have h1 : mldsaHighBits32 r = w1 := congrArg Prod.fst hdec
    have h2 : mldsaLowBits32 r = d := congrArg Prod.snd hdec
    rw [h2]; exact ⟨hdAbs, h1⟩
  · rintro ⟨hLow, hHigh⟩
    obtain ⟨_, _, _, _, hRec⟩ := decompose32_reconstruct r
    have hSub : Fq204.sub r (Fq204.ofNat (w1 * 523776)) = Fq204.ofInt (mldsaLowBits32 r) := by
      conv => lhs; rw [← hRec, hHigh, hw1Int, Fq204.ofInt_sub]
      congr 1; omega
    rw [hSub, ← Fq204.toCenteredInt_natAbs,
        Fq204.toCenteredInt_ofInt_eq (by omega) (by omega)]
    exact hLow

def makeHint32 (z r : Fq204) : Bool :=
  decide (mldsaHighBits32 r ≠ mldsaHighBits32 (Fq204.add r z))

def useHint32 (h : Bool) (r : Fq204) : Nat :=
  let (r1, r0) := decompose32 r
  if !h then r1
  else if 0 < r0 then
    if r1 + 1 = 16 then 0 else r1 + 1
  else
    if r1 = 0 then 15 else r1 - 1

theorem useHint32_makeHint32_eq_highBits32 (u ct0 : Fq204)
    (hLow : (mldsaLowBits32 u).natAbs < 261888)
    (hCt0 : Fq204.centeredAbs ct0 < 261888) :
    useHint32 (makeHint32 (Fq204.neg ct0) (Fq204.add u ct0)) (Fq204.add u ct0) =
      mldsaHighBits32 u := by
  have hCancel : Fq204.add (Fq204.add u ct0) (Fq204.neg ct0) = u := by
    rw [Fq204.add_assoc, Fq204.add_right_neg, Fq204.add_zero]
  unfold makeHint32 useHint32
  rw [hCancel]
  obtain ⟨hu1Lt, _, _, -, huRec⟩ := decompose32_reconstruct u
  let u1 := mldsaHighBits32 u
  let u0 := mldsaLowBits32 u
  let e := Fq204.toCenteredInt ct0
  have hu0Bounds : -261888 < u0 ∧ u0 < 261888 := by dsimp [u0]; constructor <;> omega
  have heAbs : e.natAbs < 261888 := by dsimp [e]; rwa [Fq204.toCenteredInt_natAbs]
  have heBounds : -261888 < e ∧ e < 261888 := by constructor <;> omega
  have hrEq : Fq204.add u ct0 = Fq204.ofInt ((u1 : Int) * 523776 + (u0 + e)) := by
    conv => lhs; rw [← huRec, ← Fq204.ofInt_toCenteredInt ct0]
    rw [Fq204.ofInt_add]; dsimp [u1, u0, e]; rw [Int.add_assoc]
  let s := u0 + e
  if hsMid : -261888 < s ∧ s ≤ 261888 then
    have hdecR : decompose32 (Fq204.add u ct0) = (u1, s) := by
      rw [hrEq]; exact decompose32_ofInt_interior hu1Lt (Or.inl hsMid.1) hsMid.2
    have hr1 : mldsaHighBits32 (Fq204.add u ct0) = u1 := by unfold mldsaHighBits32; rw [hdecR]
    change (let (r1, r0) := decompose32 (Fq204.add u ct0)
            if !decide (mldsaHighBits32 (Fq204.add u ct0) ≠ u1) then r1
            else if 0 < r0 then if r1 + 1 = 16 then 0 else r1 + 1
            else if r1 = 0 then 15 else r1 - 1) = u1
    rw [hdecR, hr1]
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.not_false, ↓reduceIte]
  else if hsHi : 261888 < s then
    clear hsMid
    let w0 := s - 523776
    have hw0Bounds : -261888 < w0 ∧ w0 < 0 := by dsimp [w0, s] at *; constructor <;> omega
    if hu1Top : u1 + 1 = 16 then
      have hu1Val : u1 = 15 := by omega
      have hrEqWrap : Fq204.add u ct0 = Fq204.ofInt (((0 : Nat) : Int) * 523776 + (w0 - 1)) := by
        rw [hrEq]; apply Fq204.ext; apply Int.ofNat_inj.mp
        rw [Fq204.ofInt_val, Fq204.ofInt_val]; unfold mldsaQ
        have hDiff : (u1 : Int) * 523776 + (u0 + e) =
            (((0 : Nat) : Int) * 523776 + (w0 - 1)) + ((8380417 : Nat) : Int) := by
          dsimp [w0, s] at *; omega
        rw [hDiff, Int.add_emod_right]
      have hdecR : decompose32 (Fq204.add u ct0) = (0, w0 - 1) := by
        rw [hrEqWrap]
        exact decompose32_ofInt_interior (u1 := 0) (u0 := w0 - 1) (by omega)
          (by if hInt : -261888 < w0 - 1 then exact Or.inl hInt else exact Or.inr ⟨rfl, by omega⟩)
          (by omega)
      have hr1 : mldsaHighBits32 (Fq204.add u ct0) = 0 := by unfold mldsaHighBits32; rw [hdecR]
      have hne : (0 : Nat) ≠ u1 := by omega
      have hnPos : ¬ (0 < w0 - 1) := by omega
      change (let (r1, r0) := decompose32 (Fq204.add u ct0)
              if !decide (mldsaHighBits32 (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 16 then 0 else r1 + 1
              else if r1 = 0 then 15 else r1 - 1) = u1
      rw [hdecR, hr1, decide_eq_true hne]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnPos]
      omega
    else
      have hrEqCarry : Fq204.add u ct0 = Fq204.ofInt (((u1 + 1 : Nat) : Int) * 523776 + w0) := by
        rw [hrEq]; apply congrArg Fq204.ofInt; dsimp [w0, s]; omega
      have hdecR : decompose32 (Fq204.add u ct0) = (u1 + 1, w0) := by
        rw [hrEqCarry]
        exact decompose32_ofInt_interior (u1 := u1 + 1) (u0 := w0) (by omega) (Or.inl hw0Bounds.1) (by omega)
      have hr1 : mldsaHighBits32 (Fq204.add u ct0) = u1 + 1 := by unfold mldsaHighBits32; rw [hdecR]
      have hne : u1 + 1 ≠ u1 := by omega
      have hnPos : ¬ (0 < w0) := by omega
      have hnz : u1 + 1 ≠ 0 := by omega
      change (let (r1, r0) := decompose32 (Fq204.add u ct0)
              if !decide (mldsaHighBits32 (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 16 then 0 else r1 + 1
              else if r1 = 0 then 15 else r1 - 1) = u1
      rw [hdecR, hr1, decide_eq_true hne]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnPos, hnz]
      omega
  else
    have hsLe : s ≤ -261888 :=
      Int.not_lt.mp (fun h => hsMid ⟨h, Int.not_lt.mp hsHi⟩)
    clear hsMid
    if hsExactZero : u1 = 0 ∧ s = -261888 then
      rcases hsExactZero with ⟨hu1Zero, hsEq⟩
      have hSumEq : u0 + e = -261888 := hsEq
      have hdecR : decompose32 (Fq204.add u ct0) = (0, -261888) := by
        rw [hrEq, hu1Zero, hSumEq]; decide
      have hr1 : mldsaHighBits32 (Fq204.add u ct0) = 0 := by unfold mldsaHighBits32; rw [hdecR]
      change (let (r1, r0) := decompose32 (Fq204.add u ct0)
              if !decide (mldsaHighBits32 (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 16 then 0 else r1 + 1
              else if r1 = 0 then 15 else r1 - 1) = u1
      rw [hdecR, hr1, hu1Zero]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.not_false, ↓reduceIte]
    else
      let w0 := s + 523776
      if hu1Zero : u1 = 0 then
        have hsNe : s ≠ -261888 := fun h => hsExactZero ⟨hu1Zero, h⟩
        clear hsExactZero
        have hsLt : s < -261888 := by omega
        have hw0Bounds : 0 < w0 ∧ w0 < 261888 := by dsimp [w0, s] at *; constructor <;> omega
        have hrEqBorrow : Fq204.add u ct0 = Fq204.ofInt (((15 : Nat) : Int) * 523776 + (w0 + 1)) := by
          rw [hrEq]; apply Fq204.ext; apply Int.ofNat_inj.mp
          rw [Fq204.ofInt_val, Fq204.ofInt_val]; unfold mldsaQ
          have hDiff : ((u1 : Int) * 523776 + (u0 + e)) + ((8380417 : Nat) : Int) =
              ((15 : Nat) : Int) * 523776 + (w0 + 1) := by
            dsimp [w0, s] at *; omega
          rw [← Int.add_emod_right ((u1 : Int) * 523776 + (u0 + e)) ((8380417 : Nat) : Int), hDiff]
        have hdecR : decompose32 (Fq204.add u ct0) = (15, w0 + 1) := by
          rw [hrEqBorrow]
          exact decompose32_ofInt_interior (u1 := 15) (u0 := w0 + 1) (by omega) (Or.inl (by omega)) (by omega)
        have hr1 : mldsaHighBits32 (Fq204.add u ct0) = 15 := by unfold mldsaHighBits32; rw [hdecR]
        have hne : (15 : Nat) ≠ u1 := by omega
        have hPos : 0 < w0 + 1 := by omega
        change (let (r1, r0) := decompose32 (Fq204.add u ct0)
                if !decide (mldsaHighBits32 (Fq204.add u ct0) ≠ u1) then r1
                else if 0 < r0 then if r1 + 1 = 16 then 0 else r1 + 1
                else if r1 = 0 then 15 else r1 - 1) = u1
        rw [hdecR, hr1, decide_eq_true hne]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPos]
        omega
      else
        clear hsExactZero
        have hw0Bounds : 0 < w0 ∧ w0 ≤ 261888 := by dsimp [w0, s] at *; constructor <;> omega
        have hrEqBorrow : Fq204.add u ct0 = Fq204.ofInt (((u1 - 1 : Nat) : Int) * 523776 + w0) := by
          rw [hrEq]; apply congrArg Fq204.ofInt; dsimp [w0, s]; omega
        have hdecR : decompose32 (Fq204.add u ct0) = (u1 - 1, w0) := by
          rw [hrEqBorrow]
          exact decompose32_ofInt_interior (u1 := u1 - 1) (u0 := w0) (by omega) (Or.inl (by omega)) (by omega)
        have hr1 : mldsaHighBits32 (Fq204.add u ct0) = u1 - 1 := by unfold mldsaHighBits32; rw [hdecR]
        have hne : u1 - 1 ≠ u1 := by omega
        have hPos : 0 < w0 := by omega
        have hnTop : (u1 - 1) + 1 ≠ 16 := by omega
        change (let (r1, r0) := decompose32 (Fq204.add u ct0)
                if !decide (mldsaHighBits32 (Fq204.add u ct0) ≠ u1) then r1
                else if 0 < r0 then if r1 + 1 = 16 then 0 else r1 + 1
                else if r1 = 0 then 15 else r1 - 1) = u1
        rw [hdecR, hr1, decide_eq_true hne]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPos, hnTop]
        omega

def highBitsTree32 : {d : Nat} → PolyTree d → NatTree d
  | 0, .leaf r => .leaf (mldsaHighBits32 r)
  | _ + 1, .branch lo hi => .branch (highBitsTree32 lo) (highBitsTree32 hi)

def lowBitsNormTree32 : {d : Nat} → PolyTree d → Nat
  | 0, .leaf r => (mldsaLowBits32 r).natAbs
  | _ + 1, .branch lo hi => max (lowBitsNormTree32 lo) (lowBitsNormTree32 hi)

def makeHintTree32 : {d : Nat} → PolyTree d → PolyTree d → HintTree d
  | 0, .leaf z, .leaf r => .leaf (makeHint32 z r)
  | _ + 1, .branch z0 z1, .branch r0 r1 => .branch (makeHintTree32 z0 r0) (makeHintTree32 z1 r1)

def useHintTree32 : {d : Nat} → HintTree d → PolyTree d → NatTree d
  | 0, .leaf h, .leaf r => .leaf (useHint32 h r)
  | _ + 1, .branch h0 h1, .branch r0 r1 => .branch (useHintTree32 h0 r0) (useHintTree32 h1 r1)

def centeredDiffNormTree32 : {d : Nat} → PolyTree d → NatTree d → Nat
  | 0, .leaf r, .leaf w1 => Fq204.centeredAbs (Fq204.sub r (Fq204.ofNat (w1 * 523776)))
  | _ + 1, .branch r0 r1, .branch w0 w1 =>
    max (centeredDiffNormTree32 r0 w0) (centeredDiffNormTree32 r1 w1)

def natTreeAllLt16 : {d : Nat} → NatTree d → Prop
  | 0, .leaf w1 => w1 < 16
  | _ + 1, .branch w0 w1 => natTreeAllLt16 w0 ∧ natTreeAllLt16 w1

theorem highBitsTree32_allLt16 : ∀ {d : Nat} (p : PolyTree d), natTreeAllLt16 (highBitsTree32 p)
  | 0, .leaf r => (decompose32_reconstruct r).1
  | _ + 1, .branch p0 p1 => ⟨highBitsTree32_allLt16 p0, highBitsTree32_allLt16 p1⟩

theorem useHintTree32_makeHintTree32 : ∀ {d : Nat} (u ct0 : PolyTree d),
    lowBitsNormTree32 u < 261888 →
    PolyTree.infNorm ct0 < 261888 →
    useHintTree32 (makeHintTree32 (PolyTree.neg ct0) (PolyTree.add u ct0)) (PolyTree.add u ct0) =
      highBitsTree32 u
  | 0, .leaf u, .leaf ct0, hLow, hCt0 =>
    congrArg NatTree.leaf (useHint32_makeHint32_eq_highBits32 u ct0 hLow hCt0)
  | _ + 1, .branch u0 u1, .branch c0 c1, hLow, hCt0 => by
    simp only [lowBitsNormTree32, PolyTree.infNorm] at hLow hCt0
    simp only [PolyTree.neg, PolyTree.add, makeHintTree32, useHintTree32, highBitsTree32,
      useHintTree32_makeHintTree32 u0 c0 (by omega) (by omega),
      useHintTree32_makeHintTree32 u1 c1 (by omega) (by omega)]

theorem centeredDiffNormTree32_lt_iff : ∀ {d : Nat} (r : PolyTree d) (w1 : NatTree d) {B : Nat},
    natTreeAllLt16 w1 → B ≤ 261888 →
    (centeredDiffNormTree32 r w1 < B ↔ lowBitsNormTree32 r < B ∧ highBitsTree32 r = w1)
  | 0, .leaf r, .leaf w1, B, hw1, hB => by
    simp only [centeredDiffNormTree32, lowBitsNormTree32, highBitsTree32, NatTree.leaf.injEq]
    exact centered_diff32_lt_iff_lowBits_and_highBits r hw1 hB
  | _ + 1, .branch r0 r1, .branch w0 w1, B, hw, hB => by
    rcases hw with ⟨hw0, hw1⟩
    simp only [centeredDiffNormTree32, lowBitsNormTree32, highBitsTree32, NatTree.branch.injEq]
    have ih0 := centeredDiffNormTree32_lt_iff r0 w0 hw0 hB
    have ih1 := centeredDiffNormTree32_lt_iff r1 w1 hw1 hB
    constructor
    · intro hLt
      obtain ⟨l0, e0⟩ := ih0.mp (by omega)
      obtain ⟨l1, e1⟩ := ih1.mp (by omega)
      exact ⟨by omega, e0, e1⟩
    · rintro ⟨hLow, e0, e1⟩
      have h0 : centeredDiffNormTree32 r0 w0 < B := ih0.mpr ⟨by omega, e0⟩
      have h1 : centeredDiffNormTree32 r1 w1 < B := ih1.mpr ⟨by omega, e1⟩
      omega

/-- Parameterized FIPS 204 polynomial rounding & hint recovery structure instantiated across
    all three NIST security categories (`ML-DSA-44` `γ₂ = 95232`, `ML-DSA-65/87` `γ₂ = 261888`). -/
structure MlDsaRoundingScheme where
  gamma1 : Nat
  gamma2 : Nat
  beta : Nat
  omega : Nat
  hBetaLtGamma1 : beta < gamma1
  hBetaLtGamma2 : beta < gamma2
  highBitsOp : Poly256 → NatTree 8
  lowBitsNormOp : Poly256 → Nat
  makeHintOp : Poly256 → Poly256 → HintTree 8
  useHintOp : HintTree 8 → Poly256 → NatTree 8
  centeredDiffNormOp : Poly256 → NatTree 8 → Nat
  centeredDiff_lt_iff : ∀ (u w : Poly256),
    centeredDiffNormOp u (highBitsOp w) < gamma2 - beta ↔
      lowBitsNormOp u < gamma2 - beta ∧ highBitsOp u = highBitsOp w
  useHint_makeHint_eq : ∀ (u ct0 : Poly256),
    lowBitsNormOp u < gamma2 → PolyTree.infNorm ct0 < gamma2 →
    useHintOp (makeHintOp (PolyTree.neg ct0) (PolyTree.add u ct0)) (PolyTree.add u ct0) = highBitsOp u

def mlDsa44RoundingScheme : MlDsaRoundingScheme where
  gamma1 := 131072
  gamma2 := 95232
  beta := 78
  omega := 80
  hBetaLtGamma1 := by decide
  hBetaLtGamma2 := by decide
  highBitsOp := highBitsTree
  lowBitsNormOp := lowBitsNormTree
  makeHintOp := makeHintTree
  useHintOp := useHintTree
  centeredDiffNormOp := centeredDiffNormTree
  centeredDiff_lt_iff u w := centeredDiffNormTree_lt_iff u (highBitsTree w) (highBitsTree_allLt44 w) (by decide)
  useHint_makeHint_eq u ct0 hL hC := useHintTree_makeHintTree u ct0 hL hC

def mlDsa65RoundingScheme : MlDsaRoundingScheme where
  gamma1 := 524288
  gamma2 := 261888
  beta := 196
  omega := 55
  hBetaLtGamma1 := by decide
  hBetaLtGamma2 := by decide
  highBitsOp := highBitsTree32
  lowBitsNormOp := lowBitsNormTree32
  makeHintOp := makeHintTree32
  useHintOp := useHintTree32
  centeredDiffNormOp := centeredDiffNormTree32
  centeredDiff_lt_iff u w := centeredDiffNormTree32_lt_iff u (highBitsTree32 w) (highBitsTree32_allLt16 w) (by decide)
  useHint_makeHint_eq u ct0 hL hC := useHintTree32_makeHintTree32 u ct0 hL hC

def mlDsa87RoundingScheme : MlDsaRoundingScheme where
  gamma1 := 524288
  gamma2 := 261888
  beta := 120
  omega := 75
  hBetaLtGamma1 := by decide
  hBetaLtGamma2 := by decide
  highBitsOp := highBitsTree32
  lowBitsNormOp := lowBitsNormTree32
  makeHintOp := makeHintTree32
  useHintOp := useHintTree32
  centeredDiffNormOp := centeredDiffNormTree32
  centeredDiff_lt_iff u w := centeredDiffNormTree32_lt_iff u (highBitsTree32 w) (highBitsTree32_allLt16 w) (by decide)
  useHint_makeHint_eq u ct0 hL hC := useHintTree32_makeHintTree32 u ct0 hL hC

/-- Variable-dimension polynomial vector `R_q^d` and rectangular matrix `R_q^{k × ℓ}`
    covering `(k, ℓ) = (4, 4)` (`ML-DSA-44`), `(6, 5)` (`ML-DSA-65`), and `(8, 7)` (`ML-DSA-87`). -/
abbrev PolyFlexVec (d : Nat) := Fin d → Poly256
abbrev PolyRectMat (k ell : Nat) := Fin k → Fin ell → Poly256

def zeroFlexVec (d : Nat) : PolyFlexVec d := fun _ => PolyTree.zero 8
def addFlexVec {d : Nat} (u v : PolyFlexVec d) : PolyFlexVec d := fun i => PolyTree.add (u i) (v i)
def subFlexVec {d : Nat} (u v : PolyFlexVec d) : PolyFlexVec d := fun i => PolyTree.sub (u i) (v i)
def negFlexVec {d : Nat} (u : PolyFlexVec d) : PolyFlexVec d := fun i => PolyTree.neg (u i)
def mulPolyFlexVec {d : Nat} (c : Poly256) (v : PolyFlexVec d) : PolyFlexVec d :=
  fun i => negacyclicMul c (v i)

def flexDot : {ell : Nat} → (Fin ell → Poly256) → (Fin ell → Poly256) → Poly256
  | 0, _, _ => PolyTree.zero 8
  | _ + 1, row, v =>
    PolyTree.add (negacyclicMul (row ⟨0, Nat.zero_lt_succ _⟩) (v ⟨0, Nat.zero_lt_succ _⟩))
      (flexDot (fun j => row ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
               (fun j => v ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩))

def matVecMulRect {k ell : Nat} (A : PolyRectMat k ell) (v : PolyFlexVec ell) : PolyFlexVec k :=
  fun i => flexDot (A i) v

private theorem flexDot_add : ∀ {ell : Nat} (row u v : Fin ell → Poly256),
    flexDot row (fun j => PolyTree.add (u j) (v j)) =
      PolyTree.add (flexDot row u) (flexDot row v)
  | 0, _, _, _ => (polyTree_add_zero (PolyTree.zero 8)).symm
  | _ + 1, row, u, v => by
    dsimp only [flexDot]
    rw [negacyclicMul_left_distrib, flexDot_add, polyTree_add_add_comm]

private theorem flexDot_mulPoly : ∀ {ell : Nat} (row v : Fin ell → Poly256) (c : Poly256),
    flexDot row (fun j => negacyclicMul c (v j)) = negacyclicMul c (flexDot row v)
  | 0, _, _, c => by
    dsimp only [flexDot]
    rw [negacyclicMul_comm c (PolyTree.zero 8), negacyclicMul_zero_left]
  | _ + 1, row, v, c => by
    dsimp only [flexDot]
    have hSwap : negacyclicMul (row ⟨0, Nat.zero_lt_succ _⟩) (negacyclicMul c (v ⟨0, Nat.zero_lt_succ _⟩)) =
        negacyclicMul c (negacyclicMul (row ⟨0, Nat.zero_lt_succ _⟩) (v ⟨0, Nat.zero_lt_succ _⟩)) := by
      rw [← negacyclicMul_assoc, negacyclicMul_comm (row _) c, negacyclicMul_assoc]
    rw [hSwap, flexDot_mulPoly, ← negacyclicMul_left_distrib]

theorem matVecMulRect_add {k ell : Nat} (A : PolyRectMat k ell) (u v : PolyFlexVec ell) :
    matVecMulRect A (addFlexVec u v) = addFlexVec (matVecMulRect A u) (matVecMulRect A v) := by
  funext i; exact flexDot_add (A i) u v

theorem matVecMulRect_mulPoly {k ell : Nat} (A : PolyRectMat k ell) (c : Poly256) (v : PolyFlexVec ell) :
    matVecMulRect A (mulPolyFlexVec c v) = mulPolyFlexVec c (matVecMulRect A v) := by
  funext i; exact flexDot_mulPoly (A i) v c

def power2RoundHighFlex {d : Nat} (t : PolyFlexVec d) : PolyFlexVec d :=
  fun i => power2RoundHighTree (t i)
def power2RoundLowFlex {d : Nat} (t : PolyFlexVec d) : PolyFlexVec d :=
  fun i => power2RoundLowTree (t i)

/-- **Rectangular Module-Lattice Verification Identity (`az_sub_ct1_eq_w_sub_cs2_add_ct0_rect`)**:
    Over `R_q^k × R_q^ℓ` for arbitrary `(k, ℓ)` (including `(4,4)`, `(6,5)`, `(8,7)`),
    whenever `z = y + c · s₁`, `w = A · y`, and `t = A · s₁ + s₂ = t₁ · 2^d + t₀`,
    `A · z - c · (t₁ · 2^d) = (w - c · s₂) + c · t₀` identically in `R_q^k`. -/
theorem az_sub_ct1_eq_w_sub_cs2_add_ct0_rect {k ell : Nat}
    (A : PolyRectMat k ell) (s1 y : PolyFlexVec ell) (s2 : PolyFlexVec k) (c : Poly256) :
    let t := addFlexVec (matVecMulRect A s1) s2
    let t1Scaled := power2RoundHighFlex t
    let t0 := power2RoundLowFlex t
    let w := matVecMulRect A y
    let z := addFlexVec y (mulPolyFlexVec c s1)
    subFlexVec (matVecMulRect A z) (mulPolyFlexVec c t1Scaled) =
      addFlexVec (subFlexVec w (mulPolyFlexVec c s2)) (mulPolyFlexVec c t0) := by
  intro t t1Scaled t0 w z
  have htSplit : addFlexVec t1Scaled t0 = t := by
    funext i; exact power2RoundTree_reconstruct (t i)
  have hAz : matVecMulRect A z = addFlexVec w (mulPolyFlexVec c (matVecMulRect A s1)) := by
    dsimp [z, w]; rw [matVecMulRect_add, matVecMulRect_mulPoly]
  rw [hAz]
  funext i
  have htRow : PolyTree.add (t1Scaled i) (t0 i) = PolyTree.add (matVecMulRect A s1 i) (s2 i) :=
    congrFun htSplit i
  dsimp only [addFlexVec, subFlexVec, mulPolyFlexVec]
  apply poly256_add_left_cancel (a := negacyclicMul c (t1Scaled i))
  have hSubCancel : ∀ x y : Poly256, PolyTree.add y (PolyTree.sub x y) = x := fun x y => by
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm y, polyTree_add_assoc,
        polyTree_add_left_neg, polyTree_add_zero]
  rw [hSubCancel]
  have hRhs :
      PolyTree.add (negacyclicMul c (t1Scaled i))
        (PolyTree.add (PolyTree.sub (w i) (negacyclicMul c (s2 i))) (negacyclicMul c (t0 i))) =
      PolyTree.add (PolyTree.sub (w i) (negacyclicMul c (s2 i)))
        (negacyclicMul c (PolyTree.add (t1Scaled i) (t0 i))) := by
    rw [negacyclicMul_left_distrib, polyTree_add_comm (negacyclicMul c (t1Scaled i)),
        polyTree_add_assoc, polyTree_add_comm (negacyclicMul c (t0 i))]
  rw [hRhs, htRow, negacyclicMul_left_distrib,
      polyTree_add_comm (negacyclicMul c (matVecMulRect A s1 i)) (negacyclicMul c (s2 i)),
      ← polyTree_add_assoc, polyTree_add_comm (PolyTree.sub (w i) _), hSubCancel]

def rssMaskAddFlexEquiv {d : Nat} (target : PolyFlexVec d) :
    SimpleEquiv (PolyFlexVec d) (PolyFlexVec d) where
  toFun m := addFlexVec target m
  invFun v := subFlexVec v target
  left_inv m := by
    funext i; dsimp only [addFlexVec, subFlexVec]
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm (target i) (m i),
        polyTree_add_assoc, polyTree_add_comm (target i) (PolyTree.neg (target i)),
        polyTree_add_left_neg, polyTree_add_zero]
  right_inv v := by
    funext i; dsimp only [addFlexVec, subFlexVec]
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm (v i),
        ← polyTree_add_assoc, polyTree_add_comm (target i) (PolyTree.neg (target i)),
        polyTree_add_left_neg, polyTree_zero_add]

def finMax : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _ + 1, f => max (f ⟨0, Nat.zero_lt_succ _⟩) (finMax _ (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

private theorem finMax_lt_iff {B : Nat} (hB : 0 < B) :
    ∀ {n : Nat} (f : Fin n → Nat), finMax n f < B ↔ ∀ i : Fin n, f i < B
  | 0, _ => by
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _; exact hB
  | _ + 1, f => by
    dsimp only [finMax]
    have ih := finMax_lt_iff hB (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    constructor
    · intro hLt i
      rcases i with ⟨val, isLt⟩
      rcases val with _ | k
      · omega
      · exact ih.mp (by omega) ⟨k, Nat.lt_of_succ_lt_succ isLt⟩
    · intro hAll
      have h0 := hAll ⟨0, Nat.zero_lt_succ _⟩
      have hRest := ih.mpr (fun j => hAll ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
      omega

def infNormFlexVec {d : Nat} (v : PolyFlexVec d) : Nat :=
  finMax d (fun i => PolyTree.infNorm (v i))

def hintWeightFlexVec {k : Nat} (h : Fin k → HintTree 8) : Nat :=
  qsum k (fun i => HintTree.weight (h i))

structure ThresholdRectSignSig (k ell : Nat) where
  cTilde : List UInt8
  z : PolyFlexVec ell
  h : Fin k → HintTree 8
  usedAttempt : Nat

structure SealedRectAttemptPads (k ell : Nat) where
  maskW : PolyFlexVec k
  maskZ : PolyFlexVec ell
  maskLow : PolyFlexVec k
  maskBin : BitVec 256
  verdictBlind : Ext6Fq204

structure SealedRectSignAttemptView (k ell : Nat) where
  openedW : PolyFlexVec k
  openedZ : PolyFlexVec ell
  openedLow : PolyFlexVec k
  openedBin : BitVec 256
  openedVerdict : Ext6Fq204
  released : Option ((Fin k → NatTree 8) × ThresholdRectSignSig k ell)

def sealedRectAcceptBool {k ell : Nat} (R : MlDsaRoundingScheme)
    (chalHash : List UInt8 → (Fin k → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyRectMat k ell) (s1 y : PolyFlexVec ell) (s2 : PolyFlexVec k)
    (mu : List UInt8) : Bool :=
  let t := addFlexVec (matVecMulRect A s1) s2
  let t0 := power2RoundLowFlex t
  let w := matVecMulRect A y
  let w1 : Fin k → NatTree 8 := fun i => R.highBitsOp (w i)
  let c := sampleInBall (chalHash mu w1)
  let z := addFlexVec y (mulPolyFlexVec c s1)
  let u := subFlexVec w (mulPolyFlexVec c s2)
  let ct0 := mulPolyFlexVec c t0
  let h : Fin k → HintTree 8 := fun i => R.makeHintOp (PolyTree.neg (ct0 i)) (PolyTree.add (u i) (ct0 i))
  decide (infNormFlexVec ct0 < R.gamma2) &&
  decide (infNormFlexVec z < R.gamma1 - R.beta) &&
  decide (finMax k (fun i => R.centeredDiffNormOp (u i) (w1 i)) < R.gamma2 - R.beta) &&
  decide (hintWeightFlexVec h ≤ R.omega)

def realSealedRectAttemptView {k ell : Nat} (R : MlDsaRoundingScheme)
    (chalHash : List UInt8 → (Fin k → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyRectMat k ell) (s1 y : PolyFlexVec ell) (s2 : PolyFlexVec k)
    (mu : List UInt8) (attempt : Nat) (keccakTraceBits : BitVec 256) (failTag : Fq204)
    (pads : SealedRectAttemptPads k ell) : SealedRectSignAttemptView k ell :=
  let t := addFlexVec (matVecMulRect A s1) s2
  let t0 := power2RoundLowFlex t
  let w := matVecMulRect A y
  let w1 : Fin k → NatTree 8 := fun i => R.highBitsOp (w i)
  let cTilde := chalHash mu w1
  let c := sampleInBall cTilde
  let z := addFlexVec y (mulPolyFlexVec c s1)
  let u := subFlexVec w (mulPolyFlexVec c s2)
  let ct0 := mulPolyFlexVec c t0
  let h : Fin k → HintTree 8 := fun i => R.makeHintOp (PolyTree.neg (ct0 i)) (PolyTree.add (u i) (ct0 i))
  let accept := sealedRectAcceptBool R chalHash sampleInBall A s1 y s2 mu
  { openedW := addFlexVec w pads.maskW, openedZ := addFlexVec z pads.maskZ,
    openedLow := addFlexVec u pads.maskLow, openedBin := keccakTraceBits ^^^ pads.maskBin,
    openedVerdict := if accept then ext6Zero else ext6Scale pads.verdictBlind failTag,
    released := if accept then
      some (w1, { cTilde := cTilde, z := z, h := h, usedAttempt := attempt }) else none }

def thresholdMlDsaRectAttemptSimulator {k ell : Nat} (R : MlDsaRoundingScheme)
    (sampleInBall : List UInt8 → Poly256) (A : PolyRectMat k ell) (t1Scaled : PolyFlexVec k)
    (out : Option (ThresholdRectSignSig k ell))
    (pads : SealedRectAttemptPads k ell) : SealedRectSignAttemptView k ell :=
  match out with
  | none =>
    { openedW := pads.maskW, openedZ := pads.maskZ, openedLow := pads.maskLow,
      openedBin := pads.maskBin, openedVerdict := pads.verdictBlind, released := none }
  | some sig =>
    let c := sampleInBall sig.cTilde
    let azSubCt1 := subFlexVec (matVecMulRect A sig.z) (mulPolyFlexVec c t1Scaled)
    let w1Sim : Fin k → NatTree 8 := fun i => R.useHintOp (sig.h i) (azSubCt1 i)
    { openedW := pads.maskW, openedZ := pads.maskZ, openedLow := pads.maskLow,
      openedBin := pads.maskBin, openedVerdict := ext6Zero, released := some (w1Sim, sig) }

private def sealedRectPadsTupleEquiv (k ell : Nat) :
    SimpleEquiv (SealedRectAttemptPads k ell)
      (PolyFlexVec k × PolyFlexVec ell × PolyFlexVec k × BitVec 256 × Ext6Fq204) where
  toFun p := (p.maskW, p.maskZ, p.maskLow, p.maskBin, p.verdictBlind)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv := fun ⟨_, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _⟩ => rfl

def sealedRectAttemptPadEquiv {k ell : Nat}
    (w : PolyFlexVec k) (z : PolyFlexVec ell) (u : PolyFlexVec k)
    (keccakTraceBits : BitVec 256) (accept : Bool) (failTag : Fq204) (hFail : failTag ≠ Fq204.zero) :
    SimpleEquiv (SealedRectAttemptPads k ell) (SealedRectAttemptPads k ell) :=
  let verdictEquiv : SimpleEquiv Ext6Fq204 Ext6Fq204 :=
    if accept then SimpleEquiv.refl _ else ext6ScaleEquiv failTag hFail
  SimpleEquiv.trans (sealedRectPadsTupleEquiv k ell)
    (SimpleEquiv.trans
      (SimpleEquiv.prodCongr (rssMaskAddFlexEquiv w)
        (SimpleEquiv.prodCongr (rssMaskAddFlexEquiv z)
          (SimpleEquiv.prodCongr (rssMaskAddFlexEquiv u)
            (SimpleEquiv.prodCongr (bv256XorEquiv keccakTraceBits) verdictEquiv))))
      (SimpleEquiv.symm (sealedRectPadsTupleEquiv k ell)))

def sealedRectStepPadEquiv {k ell : Nat} (R : MlDsaRoundingScheme)
    (chalHash : List UInt8 → (Fin k → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyRectMat k ell) (s1 y : PolyFlexVec ell) (s2 : PolyFlexVec k)
    (mu : List UInt8) (keccakTraceBits : BitVec 256) (failTag : Fq204) (hFail : failTag ≠ Fq204.zero) :
    SimpleEquiv (SealedRectAttemptPads k ell) (SealedRectAttemptPads k ell) :=
  let w := matVecMulRect A y
  let w1 : Fin k → NatTree 8 := fun i => R.highBitsOp (w i)
  let c := sampleInBall (chalHash mu w1)
  sealedRectAttemptPadEquiv w (addFlexVec y (mulPolyFlexVec c s1))
    (subFlexVec w (mulPolyFlexVec c s2)) keccakTraceBits
    (sealedRectAcceptBool R chalHash sampleInBall A s1 y s2 mu) failTag hFail

def sealedRectAttemptPublicOutcome {k ell : Nat} (R : MlDsaRoundingScheme)
    (chalHash : List UInt8 → (Fin k → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyRectMat k ell) (s1 y : PolyFlexVec ell) (s2 : PolyFlexVec k)
    (mu : List UInt8) (attempt : Nat) : Option (ThresholdRectSignSig k ell) :=
  let t := addFlexVec (matVecMulRect A s1) s2
  let t0 := power2RoundLowFlex t
  let w := matVecMulRect A y
  let w1 : Fin k → NatTree 8 := fun i => R.highBitsOp (w i)
  let cTilde := chalHash mu w1
  let c := sampleInBall cTilde
  let z := addFlexVec y (mulPolyFlexVec c s1)
  let u := subFlexVec w (mulPolyFlexVec c s2)
  let ct0 := mulPolyFlexVec c t0
  let h : Fin k → HintTree 8 := fun i => R.makeHintOp (PolyTree.neg (ct0 i)) (PolyTree.add (u i) (ct0 i))
  if sealedRectAcceptBool R chalHash sampleInBall A s1 y s2 mu then
    some { cTilde := cTilde, z := z, h := h, usedAttempt := attempt }
  else none

theorem sealedRectAttempt_sim_eq_real {k ell : Nat} (R : MlDsaRoundingScheme)
    (chalHash : List UInt8 → (Fin k → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyRectMat k ell) (s1 y : PolyFlexVec ell) (s2 : PolyFlexVec k)
    (mu : List UInt8) (attempt : Nat) (keccakTraceBits : BitVec 256) (failTag : Fq204)
    (hFail : failTag ≠ Fq204.zero) (pads : SealedRectAttemptPads k ell) :
    thresholdMlDsaRectAttemptSimulator R sampleInBall A
      (power2RoundHighFlex (addFlexVec (matVecMulRect A s1) s2))
      (sealedRectAttemptPublicOutcome R chalHash sampleInBall A s1 y s2 mu attempt)
      ((sealedRectStepPadEquiv R chalHash sampleInBall A s1 y s2 mu keccakTraceBits failTag hFail).toFun pads) =
    realSealedRectAttemptView R chalHash sampleInBall A s1 y s2 mu attempt keccakTraceBits failTag pads := by
  unfold realSealedRectAttemptView sealedRectAttemptPublicOutcome
    thresholdMlDsaRectAttemptSimulator sealedRectStepPadEquiv
  dsimp only
  cases hAcc : sealedRectAcceptBool R chalHash sampleInBall A s1 y s2 mu with
  | false =>
    simp only [sealedRectAttemptPadEquiv, SimpleEquiv.trans, SimpleEquiv.prodCongr,
      SimpleEquiv.symm, sealedRectPadsTupleEquiv, rssMaskAddFlexEquiv, bv256XorEquiv,
      ext6ScaleEquiv, Bool.false_eq_true, ↓reduceIte]
  | true =>
    unfold sealedRectAcceptBool at hAcc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAcc
    rcases hAcc with ⟨⟨⟨hCt0Max, _⟩, hDiffMax⟩, _⟩
    have hG2Pos : 0 < R.gamma2 := Nat.lt_of_le_of_lt (Nat.zero_le _) R.hBetaLtGamma2
    have hG2SubPos : 0 < R.gamma2 - R.beta := Nat.sub_pos_of_lt R.hBetaLtGamma2
    have hCt0All := (finMax_lt_iff hG2Pos _).mp hCt0Max
    have hDiffAll := (finMax_lt_iff hG2SubPos _).mp hDiffMax
    let t := addFlexVec (matVecMulRect A s1) s2
    let t1Scaled := power2RoundHighFlex t
    let t0 := power2RoundLowFlex t
    let w := matVecMulRect A y
    let w1 : Fin k → NatTree 8 := fun i => R.highBitsOp (w i)
    let c := sampleInBall (chalHash mu w1)
    let z := addFlexVec y (mulPolyFlexVec c s1)
    let u := subFlexVec w (mulPolyFlexVec c s2)
    let ct0 := mulPolyFlexVec c t0
    have hId := az_sub_ct1_eq_w_sub_cs2_add_ct0_rect A s1 y s2 c
    dsimp only at hId
    have hW1Eq : (fun i : Fin k => R.useHintOp
        (R.makeHintOp (PolyTree.neg (ct0 i)) (PolyTree.add (u i) (ct0 i)))
        (subFlexVec (matVecMulRect A z) (mulPolyFlexVec c t1Scaled) i)) = w1 := by
      rw [hId]
      funext i
      dsimp only [addFlexVec, w1]
      obtain ⟨hLowI, hHighEqI⟩ := (R.centeredDiff_lt_iff (u i) (w i)).mp (hDiffAll i)
      have hLowLtG2 : R.lowBitsNormOp (u i) < R.gamma2 := Nat.lt_of_lt_of_le hLowI (Nat.sub_le _ _)
      exact (R.useHint_makeHint_eq (u i) (ct0 i) hLowLtG2 (hCt0All i)).trans hHighEqI
    simp only [sealedRectAttemptPadEquiv, SimpleEquiv.trans, SimpleEquiv.prodCongr,
      SimpleEquiv.symm, SimpleEquiv.refl, sealedRectPadsTupleEquiv, rssMaskAddFlexEquiv, bv256XorEquiv,
      ↓reduceIte]
    dsimp only [t, t1Scaled, t0, w, w1, c, z, u, ct0] at hW1Eq
    rw [hW1Eq]

structure SealedRectAttemptStepSpec (ell : Nat) where
  y : PolyFlexVec ell
  attempt : Nat
  keccakTraceBits : BitVec 256
  failTag : Fq204

def realSealedRectSignTrace {k ell : Nat} (R : MlDsaRoundingScheme)
    (chalHash : List UInt8 → (Fin k → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyRectMat k ell) (s1 : PolyFlexVec ell) (s2 : PolyFlexVec k) (mu : List UInt8) :
    (steps : List (SealedRectAttemptStepSpec ell)) →
    (Fin steps.length → SealedRectAttemptPads k ell) →
    List (SealedRectSignAttemptView k ell)
  | [], _ => []
  | stp :: rest, padFn =>
    realSealedRectAttemptView R chalHash sampleInBall A s1 stp.y s2 mu stp.attempt
      stp.keccakTraceBits stp.failTag (padFn ⟨0, Nat.zero_lt_succ _⟩) ::
    realSealedRectSignTrace R chalHash sampleInBall A s1 s2 mu rest
      (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

def thresholdMlDsaRectTraceSimulator {k ell : Nat} (R : MlDsaRoundingScheme)
    (sampleInBall : List UInt8 → Poly256) (A : PolyRectMat k ell) (t1Scaled : PolyFlexVec k) :
    (outs : List (Option (ThresholdRectSignSig k ell))) →
    (Fin outs.length → SealedRectAttemptPads k ell) →
    List (SealedRectSignAttemptView k ell)
  | [], _ => []
  | out :: rest, padFn =>
    thresholdMlDsaRectAttemptSimulator R sampleInBall A t1Scaled out (padFn ⟨0, Nat.zero_lt_succ _⟩) ::
    thresholdMlDsaRectTraceSimulator R sampleInBall A t1Scaled rest
      (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

def sealedRectTraceOutcomes {k ell : Nat} (R : MlDsaRoundingScheme)
    (chalHash : List UInt8 → (Fin k → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyRectMat k ell) (s1 : PolyFlexVec ell) (s2 : PolyFlexVec k) (mu : List UInt8)
    (steps : List (SealedRectAttemptStepSpec ell)) : List (Option (ThresholdRectSignSig k ell)) :=
  steps.map (fun stp => sealedRectAttemptPublicOutcome R chalHash sampleInBall A s1 stp.y s2 mu stp.attempt)

private def splitRectPadsEquiv (k ell n : Nat) :
    SimpleEquiv (Fin (n + 1) → SealedRectAttemptPads k ell)
      (SealedRectAttemptPads k ell × (Fin n → SealedRectAttemptPads k ell)) where
  toFun f := (f ⟨0, Nat.zero_lt_succ _⟩, fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by funext j; refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
  right_inv := fun ⟨_, _⟩ => rfl

private def consRectPadEquiv {k ell n m : Nat}
    (bijHead : SimpleEquiv (SealedRectAttemptPads k ell) (SealedRectAttemptPads k ell))
    (bijRest : SimpleEquiv (Fin n → SealedRectAttemptPads k ell) (Fin m → SealedRectAttemptPads k ell)) :
    SimpleEquiv (Fin (n + 1) → SealedRectAttemptPads k ell) (Fin (m + 1) → SealedRectAttemptPads k ell) :=
  SimpleEquiv.trans (splitRectPadsEquiv k ell n)
    (SimpleEquiv.trans (SimpleEquiv.prodCongr bijHead bijRest)
      (SimpleEquiv.symm (splitRectPadsEquiv k ell m)))

private theorem rectTraceSim_cons {k ell : Nat} (R : MlDsaRoundingScheme)
    (sampleInBall : List UInt8 → Poly256) (A : PolyRectMat k ell) (t1Scaled : PolyFlexVec k)
    (out : Option (ThresholdRectSignSig k ell)) (outsRest : List (Option (ThresholdRectSignSig k ell)))
    {n : Nat}
    (bijHead : SimpleEquiv (SealedRectAttemptPads k ell) (SealedRectAttemptPads k ell))
    (bijRest : SimpleEquiv (Fin n → SealedRectAttemptPads k ell)
                           (Fin outsRest.length → SealedRectAttemptPads k ell))
    (padFn : Fin (n + 1) → SealedRectAttemptPads k ell) :
    thresholdMlDsaRectTraceSimulator R sampleInBall A t1Scaled (out :: outsRest)
      ((consRectPadEquiv bijHead bijRest).toFun padFn) =
    thresholdMlDsaRectAttemptSimulator R sampleInBall A t1Scaled out
      (bijHead.toFun (padFn ⟨0, Nat.zero_lt_succ n⟩)) ::
    thresholdMlDsaRectTraceSimulator R sampleInBall A t1Scaled outsRest
      (bijRest.toFun (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) := rfl

/-- **Rectangular `ML-DSA-44/65/87` Sealed-`w₁` Abort-Transcript Zero-Knowledge
    (`threshold_mldsa_rect_abort_transcript_zk`)**:
    Generalizes `threshold_mldsa_abort_transcript_zk` from square `4 × 4` (`ML-DSA-44`) to arbitrary
    rectangular module dimensions `(k, ℓ)` and any FIPS 204 `MlDsaRoundingScheme` — instantiated
    constructively at `(4, 4)` (`mlDsa44RoundingScheme`), `(6, 5)` (`mlDsa65RoundingScheme`), and
    `(8, 7)` (`mlDsa87RoundingScheme`). Conditional on the public `SimAttemptOutcome` list, a
    `0-Classical` pad bijection maps `realSealedRectSignTrace` to `thresholdMlDsaRectTraceSimulator`
    using only public `(A, t₁ · 2^d)`. -/
theorem threshold_mldsa_rect_abort_transcript_zk {k ell : Nat} (R : MlDsaRoundingScheme)
    (chalHash : List UInt8 → (Fin k → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyRectMat k ell) (s1 : PolyFlexVec ell) (s2 : PolyFlexVec k) (mu : List UInt8)
    (steps : List (SealedRectAttemptStepSpec ell))
    (hFail : ∀ stp ∈ steps, stp.failTag ≠ Fq204.zero) :
    let t1Scaled := power2RoundHighFlex (addFlexVec (matVecMulRect A s1) s2)
    let outs := sealedRectTraceOutcomes R chalHash sampleInBall A s1 s2 mu steps
    ∃ (_hLen : outs.length = steps.length)
      (padBij : SimpleEquiv (Fin steps.length → SealedRectAttemptPads k ell)
                            (Fin outs.length → SealedRectAttemptPads k ell)),
      (∀ padFn,
        thresholdMlDsaRectTraceSimulator R sampleInBall A t1Scaled outs (padBij.toFun padFn) =
          realSealedRectSignTrace R chalHash sampleInBall A s1 s2 mu steps padFn) ∧
      (∀ {M : Nat} (enum : SimpleEquiv (Fin M) (Fin steps.length → SealedRectAttemptPads k ell))
         (enumOut : SimpleEquiv (Fin M) (Fin outs.length → SealedRectAttemptPads k ell))
         (D : List (SealedRectSignAttemptView k ell) → Bool),
        qsum M (fun m =>
          (D (realSealedRectSignTrace R chalHash sampleInBall A s1 s2 mu steps (enum.toFun m))).toNat) =
        qsum M (fun m =>
          (D (thresholdMlDsaRectTraceSimulator R sampleInBall A t1Scaled outs (enumOut.toFun m))).toNat)) := by
  induction steps with
  | nil => exact ⟨rfl, SimpleEquiv.refl _, (fun _ => rfl), fun _ _ _ => rfl⟩
  | cons stp rest ih =>
    have hHeadFail : stp.failTag ≠ Fq204.zero := hFail stp (.head rest)
    obtain ⟨_, bijRest, hEqRest, _⟩ := ih (fun s hs => hFail s (.tail stp hs))
    have hLenCons : (sealedRectTraceOutcomes R chalHash sampleInBall A s1 s2 mu (stp :: rest)).length =
        (stp :: rest).length := List.length_map _
    have hPointwise : ∀ padFn : Fin (rest.length + 1) → SealedRectAttemptPads k ell,
        thresholdMlDsaRectTraceSimulator R sampleInBall A
          (power2RoundHighFlex (addFlexVec (matVecMulRect A s1) s2))
          (sealedRectTraceOutcomes R chalHash sampleInBall A s1 s2 mu (stp :: rest))
          ((consRectPadEquiv (sealedRectStepPadEquiv R chalHash sampleInBall A s1 stp.y s2 mu
              stp.keccakTraceBits stp.failTag hHeadFail) bijRest).toFun padFn) =
        realSealedRectSignTrace R chalHash sampleInBall A s1 s2 mu (stp :: rest) padFn := by
      intro padFn
      have hHd := sealedRectAttempt_sim_eq_real R chalHash sampleInBall A s1 stp.y s2 mu stp.attempt
        stp.keccakTraceBits stp.failTag hHeadFail (padFn ⟨0, Nat.zero_lt_succ _⟩)
      have hTl := hEqRest (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      exact (rectTraceSim_cons R sampleInBall A (power2RoundHighFlex (addFlexVec (matVecMulRect A s1) s2))
        (sealedRectAttemptPublicOutcome R chalHash sampleInBall A s1 stp.y s2 mu stp.attempt)
        (sealedRectTraceOutcomes R chalHash sampleInBall A s1 s2 mu rest)
        (sealedRectStepPadEquiv R chalHash sampleInBall A s1 stp.y s2 mu
          stp.keccakTraceBits stp.failTag hHeadFail)
        bijRest padFn).trans (by dsimp only [realSealedRectSignTrace]; rw [hHd, hTl])
    exact ⟨hLenCons,
      consRectPadEquiv (sealedRectStepPadEquiv R chalHash sampleInBall A s1 stp.y s2 mu
        stp.keccakTraceBits stp.failTag hHeadFail) bijRest,
      hPointwise,
      fun enum enumOut D => qsum_sim_eq_of_equiv _ _ _ hPointwise enum enumOut D⟩

/-- Concrete `ML-DSA-65` (`(k, ℓ) = (6, 5)`, `γ₁ = 2^19`, `γ₂ = 261888`) specialization. -/
theorem threshold_mldsa65_abort_transcript_zk
    (chalHash : List UInt8 → (Fin 6 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyRectMat 6 5) (s1 : PolyFlexVec 5) (s2 : PolyFlexVec 6) (mu : List UInt8)
    (steps : List (SealedRectAttemptStepSpec 5))
    (hFail : ∀ stp ∈ steps, stp.failTag ≠ Fq204.zero) :
    let t1Scaled := power2RoundHighFlex (addFlexVec (matVecMulRect A s1) s2)
    let outs := sealedRectTraceOutcomes mlDsa65RoundingScheme chalHash sampleInBall A s1 s2 mu steps
    ∃ (_hLen : outs.length = steps.length)
      (padBij : SimpleEquiv (Fin steps.length → SealedRectAttemptPads 6 5)
                            (Fin outs.length → SealedRectAttemptPads 6 5)),
      (∀ padFn,
        thresholdMlDsaRectTraceSimulator mlDsa65RoundingScheme sampleInBall A t1Scaled outs
          (padBij.toFun padFn) =
        realSealedRectSignTrace mlDsa65RoundingScheme chalHash sampleInBall A s1 s2 mu steps padFn) ∧
      (∀ {M : Nat} (enum : SimpleEquiv (Fin M) (Fin steps.length → SealedRectAttemptPads 6 5))
         (enumOut : SimpleEquiv (Fin M) (Fin outs.length → SealedRectAttemptPads 6 5))
         (D : List (SealedRectSignAttemptView 6 5) → Bool),
        qsum M (fun m =>
          (D (realSealedRectSignTrace mlDsa65RoundingScheme chalHash sampleInBall A s1 s2 mu steps
            (enum.toFun m))).toNat) =
        qsum M (fun m =>
          (D (thresholdMlDsaRectTraceSimulator mlDsa65RoundingScheme sampleInBall A t1Scaled outs
            (enumOut.toFun m))).toNat)) :=
  threshold_mldsa_rect_abort_transcript_zk mlDsa65RoundingScheme chalHash sampleInBall A s1 s2 mu steps hFail

/-- Concrete `ML-DSA-87` (`(k, ℓ) = (8, 7)`, `γ₁ = 2^19`, `γ₂ = 261888`) specialization. -/
theorem threshold_mldsa87_abort_transcript_zk
    (chalHash : List UInt8 → (Fin 8 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyRectMat 8 7) (s1 : PolyFlexVec 7) (s2 : PolyFlexVec 8) (mu : List UInt8)
    (steps : List (SealedRectAttemptStepSpec 7))
    (hFail : ∀ stp ∈ steps, stp.failTag ≠ Fq204.zero) :
    let t1Scaled := power2RoundHighFlex (addFlexVec (matVecMulRect A s1) s2)
    let outs := sealedRectTraceOutcomes mlDsa87RoundingScheme chalHash sampleInBall A s1 s2 mu steps
    ∃ (_hLen : outs.length = steps.length)
      (padBij : SimpleEquiv (Fin steps.length → SealedRectAttemptPads 8 7)
                            (Fin outs.length → SealedRectAttemptPads 8 7)),
      (∀ padFn,
        thresholdMlDsaRectTraceSimulator mlDsa87RoundingScheme sampleInBall A t1Scaled outs
          (padBij.toFun padFn) =
        realSealedRectSignTrace mlDsa87RoundingScheme chalHash sampleInBall A s1 s2 mu steps padFn) ∧
      (∀ {M : Nat} (enum : SimpleEquiv (Fin M) (Fin steps.length → SealedRectAttemptPads 8 7))
         (enumOut : SimpleEquiv (Fin M) (Fin outs.length → SealedRectAttemptPads 8 7))
         (D : List (SealedRectSignAttemptView 8 7) → Bool),
        qsum M (fun m =>
          (D (realSealedRectSignTrace mlDsa87RoundingScheme chalHash sampleInBall A s1 s2 mu steps
            (enum.toFun m))).toNat) =
        qsum M (fun m =>
          (D (thresholdMlDsaRectTraceSimulator mlDsa87RoundingScheme sampleInBall A t1Scaled outs
            (enumOut.toFun m))).toNat)) :=
  threshold_mldsa_rect_abort_transcript_zk mlDsa87RoundingScheme chalHash sampleInBall A s1 s2 mu steps hFail

theorem threshold_mldsa87_rect_abort_zk_witness :
    ∃ (chalHash : List UInt8 → (Fin 8 → NatTree 8) → List UInt8)
      (sampleInBall : List UInt8 → Poly256)
      (A : PolyRectMat 8 7) (s1 : PolyFlexVec 7) (s2 : PolyFlexVec 8) (mu : List UInt8)
      (steps : List (SealedRectAttemptStepSpec 7)),
      (∀ stp ∈ steps, stp.failTag ≠ Fq204.zero) ∧
      (sealedRectTraceOutcomes mlDsa87RoundingScheme chalHash sampleInBall A s1 s2 mu steps).length =
        steps.length := by
  refine ⟨(fun _ _ => []), (fun _ => PolyTree.zero 8),
    (fun _ _ => PolyTree.zero 8), zeroFlexVec 7, zeroFlexVec 8, [],
    [{ y := zeroFlexVec 7, attempt := 0, keccakTraceBits := 0#256, failTag := Fq204.one }],
    ?_, List.length_map _⟩
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hNil
  · decide
  · cases hNil

#verify_constructive fips204ExpandMaskCoord_range fips204_asymmetric_2gamma1_plateau_shift_invariant
  tooth_closed_box_le_breaks_asymmetric_2gamma1_plateau mldsaHighBits32_eq_fips204HighBits32
  useHint32_makeHint32_eq_highBits32 az_sub_ct1_eq_w_sub_cs2_add_ct0_rect
  threshold_mldsa_rect_abort_transcript_zk threshold_mldsa65_abort_transcript_zk
  threshold_mldsa87_abort_transcript_zk
#tooth_pair fips204_asymmetric_2gamma1_plateau_shift_invariant vs
  tooth_closed_box_le_breaks_asymmetric_2gamma1_plateau
#verify_inhabited fips204_asymmetric_2gamma1_plateau_shift_invariant
  fips204_asymmetric_2gamma1_plateau_witness
#tooth_pair threshold_mldsa87_abort_transcript_zk vs
  tooth_unsealed_w1_or_irwin_hall_abort_leaks_secret
#verify_inhabited threshold_mldsa87_abort_transcript_zk threshold_mldsa87_rect_abort_zk_witness

end Qsag

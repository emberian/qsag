module
/-
# Threshold ML-DSA Abort-Transcript Zero-Knowledge, ML-DSA-65/87 Parameters & RSS Refinement

Constructive security proofs accompanying `Qsag.ThresholdMlDsaAndToprf`:

1. **NIST FIPS 204 `ML-DSA-44`, `ML-DSA-65`, and `ML-DSA-87` (`PQ128`) Parameter Verification**:
   Algebraic consistency (`β = τ · η`, `(q - 1) = highMod · 2 γ₂`, public-key and signature byte
   lengths), `η = 4` DKG nibble rejection onto `[-4, 4]`, `γ₂ = 261888` (`α = 523776`) mod-16
   `HighBits` wrap (`mlDsa65_87_highBits_bounds`), and challenge-space cardinality bounds
   `2^192 < challengeSpaceCard 39`, `2^225 < challengeSpaceCard 49`, and
   `2^256 < challengeSpaceCard 60` (`mlDsa_challenge_entropy_bounds`).

2. **Multi-Attempt Sealed-`w₁` Abort-Transcript Zero-Knowledge (`threshold_mldsa_abort_transcript_zk`)**:
   Models the hardened threshold signing transcript where `w₁` and `c` remain secret-shared inside
   RSS until all rejection predicates pass, so rejected attempts open zero `w₁`, `c`, `z`, or `h`,
   and proves across `R`-attempt traces that the joint view is simulated from public `(A, t₁)` and
   `μ` alone, together with plateau shift invariance (`fips204_z_plateau_shift_invariant`) and a
   counterexample (`tooth_unsealed_w1_or_irwin_hall_abort_leaks_secret`) showing that early `(w₁, reject)`
   openings or unflooded Irwin-Hall mask sums depend on `c · s₁`.

3. **3-Party `(2, 3)` RSS Multiplication + Sacrifice Refinement & `C(n, t - 1)` PRSS Hybrid**:
   Refines the 3-party replicated cross-term + reshare engine into `SacGate204` and
   `rssSacrificedSignStep` across multi-turn traces (`rss_distributed_trace_refines_sacrificedSignStep`),
   proves repeated-sacrifice soundness `2^256 < mldsaQ^12` (`rss3_repeated_sacrifice_pq256`), and
   instantiates the `binomRec n (t - 1)` subset-key PRSS hybrid (`rss_prss_choose_hybrid`).
-/

public import Qsag.ThresholdMlDsaAndToprf
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. NIST FIPS 204 `ML-DSA-44`, `ML-DSA-65` (Category 3) & `ML-DSA-87` (`PQ128`) Parameters -/

/-- Parameter bundle for a NIST FIPS 204 `ML-DSA` security level. -/
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

/-- `ML-DSA-44` (NIST Category 2). -/
def mlDsa44Spec : MlDsaLevelSpec :=
  { k := 4, ell := 4, gamma1 := 131072, gamma2 := 95232, tau := 39, eta := 2,
    beta := 78, omega := 80, highMod := 44, cTildeBytes := 32, zPolyBytes := 576,
    pkBytes := 1312, sigBytes := 2420 }

/-- `ML-DSA-65` (NIST Category 3). -/
def mlDsa65Spec : MlDsaLevelSpec :=
  { k := 6, ell := 5, gamma1 := 524288, gamma2 := 261888, tau := 49, eta := 4,
    beta := 196, omega := 55, highMod := 16, cTildeBytes := 48, zPolyBytes := 640,
    pkBytes := 1952, sigBytes := 3309 }

/-- `ML-DSA-87` (NIST Category 5, full `PQ128` quantum core-SVP parity). -/
def mlDsa87Spec : MlDsaLevelSpec :=
  { k := 8, ell := 7, gamma1 := 524288, gamma2 := 261888, tau := 60, eta := 2,
    beta := 120, omega := 75, highMod := 16, cTildeBytes := 64, zPolyBytes := 640,
    pkBytes := 2592, sigBytes := 4627 }

/-- Algebraic and wire-format consistency check for a FIPS 204 `ML-DSA` parameter set. -/
def mlDsaLevelWellFormed (p : MlDsaLevelSpec) : Bool :=
  decide (p.beta = p.tau * p.eta) &&
  decide (mldsaQ - 1 = p.highMod * (2 * p.gamma2)) &&
  decide (p.beta < p.gamma1) &&
  decide (p.beta < p.gamma2) &&
  decide (0 < p.omega ∧ p.omega ≤ 256 * p.k) &&
  decide (p.pkBytes = 32 + 320 * p.k) &&
  decide (p.sigBytes = p.cTildeBytes + p.ell * p.zPolyBytes + p.omega + p.k)

theorem mlDsa_all_three_levels_wellFormed :
    mlDsaLevelWellFormed mlDsa44Spec = true ∧
    mlDsaLevelWellFormed mlDsa65Spec = true ∧
    mlDsaLevelWellFormed mlDsa87Spec = true := by
  decide

theorem tooth_mlDsaLevelWellFormed_bad_beta :
    mlDsaLevelWellFormed { mlDsa87Spec with beta := 119 } = false := by
  decide

/-- FIPS 204 `η = 4` DKG nibble rejection (`threshold_mldsa.rs`: `b < 9 => 4 - b`). -/
def eta4SampleNibble (b : Fin 16) : Option Int :=
  if b.val < 9 then some (4 - Int.ofNat b.val) else none

theorem eta4SampleNibble_bijective_on_range :
    finSum 16 (fun b => if eta4SampleNibble b ≠ none then 1 else 0) = 9 ∧
    ∀ target : Int, -4 ≤ target → target ≤ 4 →
      finSum 16 (fun b => if eta4SampleNibble b = some target then 1 else 0) = 1 := by
  refine ⟨by decide, ?_⟩
  intro target hLo hHi
  have hCases :
      target = -4 ∨ target = -3 ∨ target = -2 ∨ target = -1 ∨ target = 0 ∨
      target = 1 ∨ target = 2 ∨ target = 3 ∨ target = 4 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- FIPS 204 `HighBits(r, 2 γ₂)` at `γ₂ = (q - 1) / 32 = 261888` (`α = 523776 = 512 * 1023`),
    used by both `ML-DSA-65` and `ML-DSA-87`. -/
def fips204HighBits32 (r : Fq204) : Nat :=
  if mldsaQ - 1 - 261888 < r.val then 0 else (r.val + 261888) / 523776

/-- For every `r ∈ F_q`, `fips204HighBits32 r` equals `((r + 261888) / 523776) % 16`
    (4-bit mod-16 wrap of the `DIVISOR_1023` quotient circuit in `threshold_mldsa.rs`) and `< 16`. -/
theorem mlDsa65_87_highBits_bounds (r : Fq204) :
    fips204HighBits32 r < 16 ∧
    fips204HighBits32 r = ((r.val + 261888) / 523776) % 16 := by
  unfold fips204HighBits32
  have hr := r.isLt
  unfold mldsaQ at hr ⊢
  if hWrap : 8380417 - 1 - 261888 < r.val then
    rw [ite_true_of hWrap]
    have hQuot : (r.val + 261888) / 523776 = 16 := by omega
    rw [hQuot]
    decide
  else
    rw [ite_false_of hWrap]
    have hLt16 : (r.val + 261888) / 523776 < 16 := by omega
    exact ⟨hLt16, (Nat.mod_eq_of_lt hLt16).symm⟩

/-- Pascal binomial coefficient `C(n, k)` for protocol subset and challenge-space counting. -/
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

private theorem factRec_pos : ∀ k : Nat, 0 < factRec k
  | 0 => Nat.zero_lt_one
  | k + 1 => Nat.mul_pos (Nat.succ_pos k) (factRec_pos k)

private theorem descFact_step_right :
    ∀ n k : Nat, descFact n (k + 1) + (k + 1) * descFact n k = (n + 1) * descFact n k
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | n + 1, k => by
    have ih := descFact_step_right n k
    show (n + 1) * descFact n (k + 1) + (k + 2) * ((n + 1) * descFact n k) =
      (n + 2) * ((n + 1) * descFact n k)
    have hMul : (n + 1) * descFact n (k + 1) + (n + 1) * ((k + 1) * descFact n k) =
        (n + 1) * ((n + 1) * descFact n k) := by
      rw [← Nat.left_distrib, ih]
    have hL : (k + 2) * ((n + 1) * descFact n k) =
        (n + 1) * ((k + 1) * descFact n k) + (n + 1) * descFact n k := by
      rw [Nat.succ_mul, Nat.mul_left_comm (k + 1) (n + 1)]
    have hR : (n + 2) * ((n + 1) * descFact n k) =
        (n + 1) * ((n + 1) * descFact n k) + (n + 1) * descFact n k := by
      rw [Nat.succ_mul]
    rw [hL, ← Nat.add_assoc, hMul, hR]

theorem binomRec_mul_fact : ∀ n k : Nat, binomRec n k * factRec k = descFact n k
  | _, 0 => rfl
  | 0, _ + 1 => Nat.zero_mul _
  | n + 1, k + 1 => by
    simp only [binomRec, factRec, descFact]
    rw [Nat.right_distrib]
    have h1 : binomRec n k * ((k + 1) * factRec k) = (k + 1) * (binomRec n k * factRec k) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (binomRec n k) (k + 1), Nat.mul_assoc]
    have h2 : binomRec n (k + 1) * ((k + 1) * factRec k) = binomRec n (k + 1) * factRec (k + 1) := rfl
    rw [h1, h2, binomRec_mul_fact n k, binomRec_mul_fact n (k + 1), Nat.add_comm]
    exact descFact_step_right n k

/-- Exact `SampleInBall` challenge-space cardinality `2^τ · C(256, τ)`. -/
def challengeSpaceCard (tau : Nat) : Nat :=
  2 ^ tau * binomRec 256 tau

private theorem challengeSpaceCard_gt_pow2 (tau bits : Nat)
    (h : 2 ^ bits * factRec tau < 2 ^ tau * descFact 256 tau) :
    2 ^ bits < challengeSpaceCard tau := by
  apply Nat.lt_of_mul_lt_mul_right (a := factRec tau)
  unfold challengeSpaceCard
  rw [Nat.mul_assoc, binomRec_mul_fact]
  exact h

/-- **FIPS 204 Challenge Entropy Bounds (`mlDsa_challenge_entropy_bounds`)**:
    - `ML-DSA-44` (`τ = 39`): `2^192 < 2^39 · C(256, 39)`
    - `ML-DSA-65` (`τ = 49`): `2^225 < 2^49 · C(256, 49)`
    - `ML-DSA-87` (`τ = 60`): `2^256 < 2^60 · C(256, 60)` (`≥ 128` Grover bits for `PQ128`). -/
theorem mlDsa_challenge_entropy_bounds :
    2 ^ 192 < challengeSpaceCard mlDsa44Spec.tau ∧
    2 ^ 225 < challengeSpaceCard mlDsa65Spec.tau ∧
    2 ^ 256 < challengeSpaceCard mlDsa87Spec.tau := by
  exact ⟨challengeSpaceCard_gt_pow2 39 192 (by decide),
         challengeSpaceCard_gt_pow2 49 225 (by decide),
         challengeSpaceCard_gt_pow2 60 256 (by decide)⟩

theorem mlDsa_challenge_entropy_witness :
    ∃ tau : Nat, mlDsaLevelWellFormed { mlDsa87Spec with tau := tau } = true ∧
      2 ^ 256 < challengeSpaceCard tau :=
  ⟨60, by decide, (mlDsa_challenge_entropy_bounds).2.2⟩


/-! ## §2. Sealed-`w₁` Multi-Attempt Abort-Transcript Zero-Knowledge -/

private theorem fq204_inv_mul_cancel {a : Fq204} (ha : a ≠ Fq204.zero) :
    Fq204.mul (Fq204.inv a) a = Fq204.one := by
  rw [Fq204.mul_comm, Fq204.mul_inv_cancel ha]

/-- Nonzero base-field scalar multiplication `b ↦ b · v` is a bijection on `Ext6Fq204`. -/
def ext6ScaleEquiv (v : Fq204) (hv : v ≠ Fq204.zero) : SimpleEquiv Ext6Fq204 Ext6Fq204 where
  toFun b := ext6Scale b v
  invFun u := ext6Scale u (Fq204.inv v)
  left_inv b := by
    rcases b with ⟨b0, b1, b2, b3, b4, b5⟩
    simp only [ext6Scale, Fq204.mul_assoc, Fq204.mul_inv_cancel hv, Fq204.mul_one]
  right_inv u := by
    rcases u with ⟨u0, u1, u2, u3, u4, u5⟩
    simp only [ext6Scale, Fq204.mul_assoc, fq204_inv_mul_cancel hv, Fq204.mul_one]

/-- Constructive XOR pad bijection on `BitVec 256` (`daBit` binary conversion openings). -/
def bv256XorEquiv (target : BitVec 256) : SimpleEquiv (BitVec 256) (BitVec 256) where
  toFun m := target ^^^ m
  invFun v := target ^^^ v
  left_inv m := bv_xor_cancel_left target m
  right_inv v := bv_xor_cancel_left target v

/-- Per-attempt PRSS / `daBit` / `Ext6` blinding coins for the hardened sealed-`w₁` signer. -/
structure SealedAttemptPads where
  maskW : PolyVec4
  maskZ : PolyVec4
  maskLow : PolyVec4
  maskBin : BitVec 256
  verdictBlind : Ext6Fq204

/-- Public/adversarial view of a single hardened signing attempt (`threshold_mldsa.rs`):
    - Phases 1..4 open only pad-masked shares `(openedW, openedZ, openedLow, openedBin)` and
      the `Ext6`-blinded `openedVerdict`.
    - When `released = none` (rejected attempt), **zero** `w₁`, `cTilde`, `z`, or `h` are opened.
    - When `released = some (w₁, sig)`, `openedVerdict = ext6Zero` and `(w₁, sig)` are opened jointly. -/
structure SealedSignAttemptView where
  openedW : PolyVec4
  openedZ : PolyVec4
  openedLow : PolyVec4
  openedBin : BitVec 256
  openedVerdict : Ext6Fq204
  released : Option ((Fin 4 → NatTree 8) × ThresholdSignSig)

/-- Real per-attempt view emitted by the sealed-`w₁` signer given secret `(s1, s2, y)`,
    sealed `daBit` bitstream `keccakTraceBits`, and nonzero failure indicator `failTag` when rejected. -/
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
  let cs1 := mulPolyVec4 c s1
  let cs2 := mulPolyVec4 c s2
  let ct0 := mulPolyVec4 c t0
  let z := addVec4 y cs1
  let u := subVec4 w cs2
  let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
  let accept : Bool :=
    decide (infNormVec4 ct0 < mldsa44Gamma2) &&
    decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
    decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
    decide (hintWeightVec4 h ≤ mldsa44Omega)
  { openedW := addVec4 w pads.maskW
    openedZ := addVec4 z pads.maskZ
    openedLow := addVec4 u pads.maskLow
    openedBin := keccakTraceBits ^^^ pads.maskBin
    openedVerdict := if accept then ext6Zero else ext6Scale pads.verdictBlind failTag
    released := if accept then
      some (w1, { cTilde := cTilde, z := z, h := h, usedAttempt := attempt })
    else none }

/-- Public attempt summary fed to the secret-free trace simulator:
    `none` for a rejected attempt (zero `w₁` leakage!), or `some sig` for an accepted attempt. -/
abbrev SimAttemptOutcome := Option ThresholdSignSig

/-- **Secret-Free Attempt Simulator (`thresholdMlDsaAttemptSimulator`)**:
    Uses **only** the public key `(A, t1Scaled)` and public outcome (`none` on abort, `some sig`
    on acceptance — reconstructing `w₁ = UseHint(h, A z - c t₁ 2^d)` without `(s₁, s₂)` or `y`!). -/
def thresholdMlDsaAttemptSimulator
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (t1Scaled : PolyVec4)
    (out : SimAttemptOutcome) (pads : SealedAttemptPads) : SealedSignAttemptView :=
  match out with
  | none =>
    { openedW := pads.maskW
      openedZ := pads.maskZ
      openedLow := pads.maskLow
      openedBin := pads.maskBin
      openedVerdict := pads.verdictBlind
      released := none }
  | some sig =>
    let c := sampleInBall sig.cTilde
    let w1Sim := useHintVec4 sig.h (subVec4 (matVecMul4 A sig.z) (mulPolyVec4 c t1Scaled))
    { openedW := pads.maskW
      openedZ := pads.maskZ
      openedLow := pads.maskLow
      openedBin := pads.maskBin
      openedVerdict := ext6Zero
      released := some (w1Sim, sig) }

/-- Constructive coin bijection between `SealedAttemptPads` and its tuple representation. -/
def sealedPadsTupleEquiv :
    SimpleEquiv SealedAttemptPads
      (PolyVec4 × PolyVec4 × PolyVec4 × BitVec 256 × Ext6Fq204) where
  toFun p := (p.maskW, p.maskZ, p.maskLow, p.maskBin, p.verdictBlind)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv := fun ⟨_, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _⟩ => rfl

/-- Explicit per-attempt pad/blinding bijection mapping real signer pads to simulator pads. -/
def sealedAttemptPadEquiv
    (w z u : PolyVec4) (keccakTraceBits : BitVec 256)
    (accept : Bool) (failTag : Fq204) (hFail : accept = false → failTag ≠ Fq204.zero) :
    SimpleEquiv SealedAttemptPads SealedAttemptPads :=
  let verdictEquiv : SimpleEquiv Ext6Fq204 Ext6Fq204 :=
    if hAcc : accept = false then ext6ScaleEquiv failTag (hFail hAcc)
    else SimpleEquiv.refl Ext6Fq204
  SimpleEquiv.trans sealedPadsTupleEquiv
    (SimpleEquiv.trans
      (SimpleEquiv.prodCongr (rssMaskAddEquiv w)
        (SimpleEquiv.prodCongr (rssMaskAddEquiv z)
          (SimpleEquiv.prodCongr (rssMaskAddEquiv u)
            (SimpleEquiv.prodCongr (bv256XorEquiv keccakTraceBits) verdictEquiv))))
      (SimpleEquiv.symm sealedPadsTupleEquiv))

/-- Public outcome extracted from a real attempt's deterministic algebraic core. -/
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
  let accept : Bool :=
    decide (infNormVec4 ct0 < mldsa44Gamma2) &&
    decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
    decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
    decide (hintWeightVec4 h ≤ mldsa44Omega)
  if accept then some { cTilde := cTilde, z := z, h := h, usedAttempt := attempt } else none

/-- Single-attempt simulation exactness: on both rejected attempts (`released = none`) and
    accepted attempts (`w₁` reconstructed via `UseHint` from public `(A, t₁)`), `sealedAttemptPadEquiv`
    makes `thresholdMlDsaAttemptSimulator` match `realSealedAttemptView` pointwise. -/
theorem sealedAttempt_sim_eq_real
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 y : PolyVec4) (mu : List UInt8) (attempt : Nat)
    (keccakTraceBits : BitVec 256) (failTag : Fq204)
    (hFail : failTag ≠ Fq204.zero) (pads : SealedAttemptPads) :
    let t1Scaled := power2RoundHighVec4 (addVec4 (matVecMul4 A s1) s2)
    let w := matVecMul4 A y
    let w1 := highBitsVec4 w
    let c := sampleInBall (chalHash mu w1)
    let z := addVec4 y (mulPolyVec4 c s1)
    let u := subVec4 w (mulPolyVec4 c s2)
    let ct0 := mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 A s1) s2))
    let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
    let accept : Bool :=
      decide (infNormVec4 ct0 < mldsa44Gamma2) &&
      decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
      decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
      decide (hintWeightVec4 h ≤ mldsa44Omega)
    let e := sealedAttemptPadEquiv w z u keccakTraceBits accept failTag (fun _ => hFail)
    thresholdMlDsaAttemptSimulator sampleInBall A t1Scaled
      (sealedAttemptPublicOutcome chalHash sampleInBall A s1 s2 y mu attempt)
      (e.toFun pads) =
    realSealedAttemptView chalHash sampleInBall A s1 s2 y mu attempt keccakTraceBits failTag pads := by
  intro t1Scaled w w1 c z u ct0 h accept e
  unfold realSealedAttemptView sealedAttemptPublicOutcome thresholdMlDsaAttemptSimulator
  dsimp only [w, w1, c, z, u, ct0, h, accept, e]
  cases hAcc :
      (decide (infNormVec4 ct0 < mldsa44Gamma2) &&
       decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
       decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
       decide (hintWeightVec4 h ≤ mldsa44Omega)) with
  | false =>
    dsimp only [sealedAttemptPadEquiv, SimpleEquiv.trans, SimpleEquiv.prodCongr,
      SimpleEquiv.symm, sealedPadsTupleEquiv, rssMaskAddEquiv, bv256XorEquiv,
      ext6ScaleEquiv, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true]
  | true =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAcc
    rcases hAcc with ⟨⟨⟨hCt0, _⟩, hDiff⟩, _⟩
    have hB : mldsa44Gamma2 - mldsa44Beta ≤ 95232 := by decide
    obtain ⟨hLow, hHighEq⟩ := (centeredDiffNormVec4_lt_iff u w hB).mp hDiff
    have hUseHint := highBits_az_sub_ct_eq_w1 A s1 s2 y c mldsa44Beta hLow hCt0
    dsimp only at hUseHint
    have hW1Eq : useHintVec4 h (subVec4 (matVecMul4 A z) (mulPolyVec4 c t1Scaled)) = w1 :=
      hUseHint.trans hHighEq
    dsimp only [sealedAttemptPadEquiv, SimpleEquiv.trans, SimpleEquiv.prodCongr,
      SimpleEquiv.symm, SimpleEquiv.refl, sealedPadsTupleEquiv, rssMaskAddEquiv, bv256XorEquiv,
      Bool.true_eq_false, ↓reduceDIte, ↓reduceIte]
    rw [hW1Eq]

/-- Multi-attempt step specification for an `R`-attempt signing session. -/
structure SealedAttemptStepSpec where
  y : PolyVec4
  attempt : Nat
  keccakTraceBits : BitVec 256
  failTag : Fq204

/-- Multi-attempt real signing view trace over `R` attempts (`List SealedAttemptStepSpec`). -/
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

/-- Multi-attempt secret-free simulator trace parameterized only by `(A, t1Scaled)` and outcomes. -/
def thresholdMlDsaTraceSimulator
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (t1Scaled : PolyVec4) :
    (outs : List SimAttemptOutcome) → (Fin outs.length → SealedAttemptPads) →
    List SealedSignAttemptView
  | [], _ => []
  | out :: rest, padFn =>
    thresholdMlDsaAttemptSimulator sampleInBall A t1Scaled out (padFn ⟨0, Nat.zero_lt_succ _⟩) ::
    thresholdMlDsaTraceSimulator sampleInBall A t1Scaled rest
      (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

/-- Public outcome list across an `R`-attempt trace. -/
def sealedTraceOutcomes
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 : PolyVec4) (mu : List UInt8)
    (steps : List SealedAttemptStepSpec) : List SimAttemptOutcome :=
  steps.map (fun stp => sealedAttemptPublicOutcome chalHash sampleInBall A s1 s2 stp.y mu stp.attempt)

/-- **Abort-Transcript Zero-Knowledge Simulation Theorem (`threshold_mldsa_abort_transcript_zk`)**:
    Across any `R`-attempt signing trace where every rejected attempt carries a nonzero `failTag`,
    there is an explicit `0-Classical` bijection `SimpleEquiv` on the `R`-attempt pad tape such that
    `thresholdMlDsaTraceSimulator` (using **only** public `(A, t1Scaled)` and `SimAttemptOutcome`,
    with **zero** `w₁` opened on aborts and **zero** `(s₁, s₂)` access) matches `realSealedSignTrace`
    pointwise and induces identical distinguisher hit counts over any finite coin enumeration. -/
theorem threshold_mldsa_abort_transcript_zk
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (s1 s2 : PolyVec4) (mu : List UInt8)
    (steps : List SealedAttemptStepSpec)
    (hFail : ∀ stp ∈ steps, stp.failTag ≠ Fq204.zero) :
    let t1Scaled := power2RoundHighVec4 (addVec4 (matVecMul4 A s1) s2)
    let outs := sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu steps
    ∃ (hLen : outs.length = steps.length)
      (padBij : SimpleEquiv (Fin steps.length → SealedAttemptPads)
                            (Fin outs.length → SealedAttemptPads)),
      (∀ padFn,
        thresholdMlDsaTraceSimulator sampleInBall A t1Scaled outs (padBij.toFun padFn) =
          realSealedSignTrace chalHash sampleInBall A s1 s2 mu steps padFn) ∧
      (∀ {M : Nat} (enum : SimpleEquiv (Fin M) (Fin steps.length → SealedAttemptPads))
         (enumOut : SimpleEquiv (Fin M) (Fin outs.length → SealedAttemptPads))
         (D : List SealedSignAttemptView → Bool),
        finSum M (fun m =>
          (D (realSealedSignTrace chalHash sampleInBall A s1 s2 mu steps (enum.toFun m))).toNat) =
        finSum M (fun m =>
          (D (thresholdMlDsaTraceSimulator sampleInBall A t1Scaled outs (enumOut.toFun m))).toNat)) := by
  induction steps with
  | nil =>
    refine ⟨rfl, SimpleEquiv.refl _, (fun _ => rfl), ?_⟩
    intro M enum enumOut D
    rfl
  | cons stp rest ih =>
    have hHeadFail : stp.failTag ≠ Fq204.zero := hFail stp (.head rest)
    obtain ⟨hLenRest, bijRest, hEqRest, _⟩ :=
      ih (fun s hs => hFail s (.tail stp hs))
    let w := matVecMul4 A stp.y
    let w1 := highBitsVec4 w
    let c := sampleInBall (chalHash mu w1)
    let z := addVec4 stp.y (mulPolyVec4 c s1)
    let u := subVec4 w (mulPolyVec4 c s2)
    let ct0 := mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 A s1) s2))
    let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
    let accept : Bool :=
      decide (infNormVec4 ct0 < mldsa44Gamma2) &&
      decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
      decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
      decide (hintWeightVec4 h ≤ mldsa44Omega)
    let bijHead := sealedAttemptPadEquiv w z u stp.keccakTraceBits accept stp.failTag
      (fun _ => hHeadFail)
    have hLenCons : (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu (stp :: rest)).length =
        (stp :: rest).length := by simp [sealedTraceOutcomes]
    let splitIn : SimpleEquiv (Fin (rest.length + 1) → SealedAttemptPads)
        (SealedAttemptPads × (Fin rest.length → SealedAttemptPads)) :=
      { toFun := fun f => (f ⟨0, Nat.zero_lt_succ _⟩, fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        invFun := fun p => Fin.cases p.1 p.2
        left_inv := fun f => by
          funext j
          refine Fin.cases ?_ (fun i => ?_) j <;> rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    let outsRest := sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu rest
    let splitOut : SimpleEquiv (Fin (outsRest.length + 1) → SealedAttemptPads)
        (SealedAttemptPads × (Fin outsRest.length → SealedAttemptPads)) :=
      { toFun := fun f => (f ⟨0, Nat.zero_lt_succ _⟩, fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        invFun := fun p => Fin.cases p.1 p.2
        left_inv := fun f => by
          funext j
          refine Fin.cases ?_ (fun i => ?_) j <;> rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    let bijCons : SimpleEquiv (Fin (rest.length + 1) → SealedAttemptPads)
        (Fin (outsRest.length + 1) → SealedAttemptPads) :=
      SimpleEquiv.trans splitIn
        (SimpleEquiv.trans (SimpleEquiv.prodCongr bijHead bijRest) (SimpleEquiv.symm splitOut))
    have hPointwise : ∀ padFn : Fin (rest.length + 1) → SealedAttemptPads,
        thresholdMlDsaTraceSimulator sampleInBall A
          (power2RoundHighVec4 (addVec4 (matVecMul4 A s1) s2))
          (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu (stp :: rest))
          (bijCons.toFun padFn) =
        realSealedSignTrace chalHash sampleInBall A s1 s2 mu (stp :: rest) padFn := by
      intro padFn
      have hHd := sealedAttempt_sim_eq_real chalHash sampleInBall A s1 s2 stp.y mu stp.attempt
        stp.keccakTraceBits stp.failTag hHeadFail (padFn ⟨0, Nat.zero_lt_succ _⟩)
      have hTl := hEqRest (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      dsimp only [sealedTraceOutcomes, List.map, thresholdMlDsaTraceSimulator, realSealedSignTrace,
        bijCons, SimpleEquiv.trans, SimpleEquiv.prodCongr, SimpleEquiv.symm, splitIn, splitOut]
      have hZero : (Fin.cases (bijHead.toFun (padFn ⟨0, Nat.zero_lt_succ _⟩))
          (bijRest.toFun (fun i => padFn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) :
          Fin (outsRest.length + 1) → SealedAttemptPads) ⟨0, Nat.zero_lt_succ _⟩ =
          bijHead.toFun (padFn ⟨0, Nat.zero_lt_succ _⟩) := rfl
      have hSucc : (fun i : Fin outsRest.length =>
          (Fin.cases (bijHead.toFun (padFn ⟨0, Nat.zero_lt_succ _⟩))
            (bijRest.toFun (fun k => padFn ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩)) :
            Fin (outsRest.length + 1) → SealedAttemptPads) ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
          bijRest.toFun (fun k => padFn ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩) := rfl
      rw [hZero, hSucc, hHd, hTl]
    refine ⟨hLenCons, bijCons, hPointwise, ?_⟩
    intro M enum enumOut D
    let perm : Fin M → Fin M := fun m => enumOut.invFun (bijCons.toFun (enum.toFun m))
    let permInv : Fin M → Fin M := fun m => enum.invFun (bijCons.invFun (enumOut.toFun m))
    have hL : ∀ m, permInv (perm m) = m := fun m => by
      dsimp only [perm, permInv]
      rw [enumOut.right_inv, bijCons.left_inv, enum.left_inv]
    have hR : ∀ m, perm (permInv m) = m := fun m => by
      dsimp only [perm, permInv]
      rw [enum.right_inv, bijCons.right_inv, enumOut.left_inv]
    have hCong : ∀ m : Fin M,
        (D (realSealedSignTrace chalHash sampleInBall A s1 s2 mu (stp :: rest) (enum.toFun m))).toNat =
        (D (thresholdMlDsaTraceSimulator sampleInBall A
          (power2RoundHighVec4 (addVec4 (matVecMul4 A s1) s2))
          (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu (stp :: rest))
          (enumOut.toFun (perm m)))).toNat := by
      intro m
      dsimp only [perm]
      rw [enumOut.right_inv, hPointwise]
    rw [finSum_congr hCong]
    exact finSum_perm_invariant perm permInv hL hR
      (fun m => (D (thresholdMlDsaTraceSimulator sampleInBall A
        (power2RoundHighVec4 (addVec4 (matVecMul4 A s1) s2))
        (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu (stp :: rest))
        (enumOut.toFun m))).toNat)

/-- Coordinate-level FIPS 204 plateau mask box `[-(γ₁ - 1), γ₁ - 1]` (`2 γ₁ - 1` elements). -/
def maskCoordAt (gamma1 : Nat) (idx : Fin (2 * gamma1 - 1)) : Int :=
  Int.ofNat idx.val - (Int.ofNat gamma1 - 1)

/-- Open rejection box `|z| < B`, i.e., `-B < z ∧ z < B`. -/
def inOpenNormBox (B : Nat) (z : Int) : Bool :=
  decide (-(Int.ofNat B) < z ∧ z < Int.ofNat B)

/-- **Plateau Shift-Invariance (`fips204_z_plateau_shift_invariant`)**:
    Over the uniform mask box `y ∈ [-(γ₁ - 1), γ₁ - 1]`, for every secret shift `cs1 ∈ [-β, β]`
    and every target `zStar` inside the acceptance plateau `|zStar| < γ₁ - β`, there is a unique
    mask index `idx` with `maskCoordAt γ₁ idx + cs1 = zStar`, so every accepted `zStar` has exact
    multiplicity `1` independent of `cs1`. -/
theorem fips204_z_plateau_shift_invariant
    (gamma1 beta : Nat) (hLt : beta < gamma1)
    (cs1 zStar : Int)
    (hCs1 : -(Int.ofNat beta) ≤ cs1 ∧ cs1 ≤ Int.ofNat beta)
    (hBox : inOpenNormBox (gamma1 - beta) zStar = true) :
    finSum (2 * gamma1 - 1) (fun idx =>
      if maskCoordAt gamma1 idx + cs1 = zStar then 1 else 0) = 1 := by
  unfold inOpenNormBox at hBox
  have hZ := of_decide_eq_true hBox
  let kNat : Nat := (zStar - cs1 + (Int.ofNat gamma1 - 1)).toNat
  have hkLt : kNat < 2 * gamma1 - 1 := by omega
  let targetIdx : Fin (2 * gamma1 - 1) := ⟨kNat, hkLt⟩
  have hiff : ∀ idx : Fin (2 * gamma1 - 1),
      (if maskCoordAt gamma1 idx + cs1 = zStar then 1 else 0) =
      (if idx = targetIdx then 1 else 0) := by
    intro idx
    unfold maskCoordAt
    have hi := idx.isLt
    if hEq : idx = targetIdx then
      rw [ite_true_of hEq, hEq]
      have hMatch : Int.ofNat targetIdx.val - (Int.ofNat gamma1 - 1) + cs1 = zStar := by
        dsimp only [targetIdx, kNat]
        omega
      rw [ite_true_of hMatch]
    else
      rw [ite_false_of hEq]
      have hValNe : idx.val ≠ kNat := fun hv => hEq (Fin.ext hv)
      have hNeZ : Int.ofNat idx.val - (Int.ofNat gamma1 - 1) + cs1 ≠ zStar := by
        intro hz
        apply hValNe
        dsimp only [kNat]
        omega
      rw [ite_false_of hNeZ]
  rw [finSum_congr hiff]
  exact finSum_eq_indicator (2 * gamma1 - 1) targetIdx

/-- Unsealed early-`w₁` abort predicate on a toy coordinate (`w₁ = (y + 4) / 2`, `|y + cs1| < 3`),
    and 2-party narrow Irwin-Hall sum-of-uniforms hit count `y = y₁ + y₂` (`y₁, y₂ ∈ [-2, 2]`). -/
def unsealedEarlyW1AbortHit (cs1 : Int) (idx : Fin 9) : Bool :=
  let y := maskCoordAt 5 idx
  let w1 := (y + 4) / 2
  decide (w1 = 4) && !inOpenNormBox 3 (y + cs1)

def irwinHall2HitCount (cs1 zTarget : Int) : Nat :=
  finSum 5 (fun i => finSum 5 (fun j =>
    if (Int.ofNat i.val - 2) + (Int.ofNat j.val - 2) + cs1 = zTarget then 1 else 0))

/-- **`#tooth` (`tooth_unsealed_w1_or_irwin_hall_abort_leaks_secret`)**:
    1. **Early `(w₁, reject)` Leakage**: Opening `w₁` before rejection (`unsealedEarlyW1AbortHit`)
       yields `2` top-bucket aborts under `cs₁ = 0` vs `1` under `cs₁ = 1` (`≠`), whereas the
       sealed simulator `thresholdMlDsaAttemptSimulator _ _ _ none` opens `released = none`!
    2. **Irwin-Hall Sum-of-Uniforms Leakage**: Summing two narrow uniform masks `y₁ + y₂` without
       canonical PRSS/flooding plateau uniformity gives `5` hits at `z = 0` for `cs₁ = 0` vs `4`
       hits for `cs₁ = 1` (`≠`), whereas `fips204_z_plateau_shift_invariant` gives constant `1`! -/
theorem tooth_unsealed_w1_or_irwin_hall_abort_leaks_secret
    (sampleInBall : List UInt8 → Poly256) (A : PolyMat4) (t1 : PolyVec4) (pads : SealedAttemptPads) :
    (thresholdMlDsaAttemptSimulator sampleInBall A t1 none pads).released = none ∧
    finSum 9 (fun idx => (unsealedEarlyW1AbortHit 0 idx).toNat) ≠
      finSum 9 (fun idx => (unsealedEarlyW1AbortHit 1 idx).toNat) ∧
    irwinHall2HitCount 0 0 ≠ irwinHall2HitCount 1 0 := by
  exact ⟨rfl, by decide, by decide⟩

theorem threshold_mldsa_abort_zk_witness :
    ∃ (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
      (sampleInBall : List UInt8 → Poly256)
      (A : PolyMat4) (s1 s2 : PolyVec4) (mu : List UInt8)
      (steps : List SealedAttemptStepSpec),
      (∀ stp ∈ steps, stp.failTag ≠ Fq204.zero) ∧
      ∃ (hLen : (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu steps).length = steps.length)
        (padBij : SimpleEquiv (Fin steps.length → SealedAttemptPads)
          (Fin (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu steps).length → SealedAttemptPads)),
        ∀ padFn,
          thresholdMlDsaTraceSimulator sampleInBall A
            (power2RoundHighVec4 (addVec4 (matVecMul4 A s1) s2))
            (sealedTraceOutcomes chalHash sampleInBall A s1 s2 mu steps) (padBij.toFun padFn) =
          realSealedSignTrace chalHash sampleInBall A s1 s2 mu steps padFn := by
  let stp : SealedAttemptStepSpec :=
    { y := rssZeroVec4, attempt := 0, keccakTraceBits := 0#256, failTag := Fq204.one }
  have hFail : ∀ s ∈ [stp], s.failTag ≠ Fq204.zero := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hNil
    · decide
    · cases hNil
  obtain ⟨hLen, padBij, hEq, _⟩ := threshold_mldsa_abort_transcript_zk
    (fun _ _ => []) (fun _ => PolyTree.zero 8) idMat4 rssZeroVec4 rssZeroVec4 [] [stp] hFail
  exact ⟨(fun _ _ => []), (fun _ => PolyTree.zero 8), idMat4, rssZeroVec4, rssZeroVec4,
    [], [stp], hFail, hLen, padBij, hEq⟩


/-! ## §3. 3-Party `(2, 3)` RSS Multiplication + Sacrifice Refinement & `C(n, t - 1)` PRSS Hybrid -/

/-- `(2, 3)` replicated secret share over `Fq204`:
    Party 0 holds `(s1, s2)`, Party 1 holds `(s0, s2)`, Party 2 holds `(s0, s1)`. -/
structure Rss3Share where
  s0 : Fq204
  s1 : Fq204
  s2 : Fq204
  deriving DecidableEq, Repr

/-- Reconstruct the shared field element `s0 + s1 + s2` in `Fq204`. -/
def rss3Recon (x : Rss3Share) : Fq204 :=
  Fq204.add (Fq204.add x.s0 x.s1) x.s2

/-- Disjoint 3-party cross-term inner-product + zero-sum PRSS reshare (`rss_mpc.rs` `Engine::mul`),
    allowing an adversarial additive reshare shift `delta` on Party 0's outgoing share. -/
def rss3MulStep (x y : Rss3Share) (r0 r1 : Fq204) (delta : Fq204) : Rss3Share :=
  let u0 := Fq204.add (Fq204.add (Fq204.mul x.s1 y.s1) (Fq204.mul x.s1 y.s2)) (Fq204.mul x.s2 y.s1)
  let u1 := Fq204.add (Fq204.add (Fq204.mul x.s2 y.s2) (Fq204.mul x.s2 y.s0)) (Fq204.mul x.s0 y.s2)
  let u2 := Fq204.add (Fq204.add (Fq204.mul x.s0 y.s0) (Fq204.mul x.s0 y.s1)) (Fq204.mul x.s1 y.s0)
  let r2 := Fq204.neg (Fq204.add r0 r1)
  { s0 := Fq204.add (Fq204.add u0 r0) delta
    s1 := Fq204.add u1 r1
    s2 := Fq204.add u2 r2 }

/-- Exact reconstruction law for 3-party RSS multiplication:
    `rss3Recon (rss3MulStep x y r0 r1 delta) = rss3Recon x * rss3Recon y + delta`. -/
theorem rss3MulStep_recon (x y : Rss3Share) (r0 r1 delta : Fq204) :
    rss3Recon (rss3MulStep x y r0 r1 delta) =
      Fq204.add (Fq204.mul (rss3Recon x) (rss3Recon y)) delta := by
  unfold rss3Recon rss3MulStep
  dsimp only
  rw [← Fq204.ofInt_nat x.s0, ← Fq204.ofInt_nat x.s1, ← Fq204.ofInt_nat x.s2,
      ← Fq204.ofInt_nat y.s0, ← Fq204.ofInt_nat y.s1, ← Fq204.ofInt_nat y.s2,
      ← Fq204.ofInt_nat r0, ← Fq204.ofInt_nat r1, ← Fq204.ofInt_nat delta]
  simp only [Fq204.ofInt_add, Fq204.ofInt_mul, Fq204.ofInt_neg]
  congr 1
  simp only [Int.add_mul, Int.mul_add]
  omega

/-- Assemble a `SacGate204` from a 3-party RSS multiplication + sacrificial triple with shifts
    `(deltaZ, deltaC)`. -/
def rss3ToSacGate (x y : Rss3Share) (r0 r1 deltaZ : Fq204)
    (a : Ext6Fq204) (b : Rss3Share) (deltaC : Ext6Fq204) : SacGate204 :=
  { x := rss3Recon x
    y := rss3Recon y
    z := rss3Recon (rss3MulStep x y r0 r1 deltaZ)
    a := a
    b := rss3Recon b
    c := ext6Add (ext6Scale a (rss3Recon b)) deltaC }

theorem rss3ToSacGate_error_eq_delta (x y : Rss3Share) (r0 r1 deltaZ : Fq204)
    (a : Ext6Fq204) (b : Rss3Share) (deltaC : Ext6Fq204) :
    sacGateError204 (rss3ToSacGate x y r0 r1 deltaZ a b deltaC) = deltaZ := by
  unfold sacGateError204 rss3ToSacGate
  dsimp only
  rw [rss3MulStep_recon]
  rw [← Fq204.ofInt_nat (Fq204.mul (rss3Recon x) (rss3Recon y)), ← Fq204.ofInt_nat deltaZ]
  simp only [Fq204.ofInt_add, Fq204.ofInt_sub]
  have hCancel :
      (((Fq204.mul (rss3Recon x) (rss3Recon y)).val : Int) + (deltaZ.val : Int)) -
        ((Fq204.mul (rss3Recon x) (rss3Recon y)).val : Int) = (deltaZ.val : Int) := by omega
  rw [hCancel, Fq204.ofInt_nat]

/-- Repeated sacrifice checker over `chis : List Ext6Fq204` (`k`-challenge amplification). -/
def sacAcceptRepeated (chis : List Ext6Fq204) (g : SacGate204) : Bool :=
  chis.all (fun chi => sacAccept204 chi g)

/-- **Repeated Sacrifice Cheating Rejection (`rss3_repeated_sacrifice_pq256`)**:
    1. Any nonzero cheating shift `deltaZ ≠ 0` in `rss3MulStep` can pass `sacAcceptRepeated chis`
       ONLY if **every** challenge `chi ∈ chis` equals the single gate-fixed `sacBadChallenge204 g`
       (at most `1` of `q` base-field challenges per round, and `1` of `q^6` `Ext6` challenges);
    2. Repeating `k = 12` base-field challenges (or `2` `Ext6` challenges, since `(q^6)^2 = q^12`)
       satisfies `2^256 < mldsaQ^12`, i.e., cheating survival `< 2^-256` (`> 128` Grover bits). -/
theorem rss3_repeated_sacrifice_pq256
    (x y : Rss3Share) (r0 r1 deltaZ : Fq204)
    (a : Ext6Fq204) (b : Rss3Share) (deltaC : Ext6Fq204)
    (chis : List Ext6Fq204)
    (hCheat : deltaZ ≠ Fq204.zero) :
    (sacAcceptRepeated chis (rss3ToSacGate x y r0 r1 deltaZ a b deltaC) = true →
      ∀ chi ∈ chis, chi = sacBadChallenge204 (rss3ToSacGate x y r0 r1 deltaZ a b deltaC)) ∧
    2 ^ 256 < mldsaQ ^ 12 := by
  refine ⟨?_, by decide⟩
  intro hAll chi hMem
  unfold sacAcceptRepeated at hAll
  rw [List.all_eq_true] at hAll
  rcases sacAccept204_sound (hAll chi hMem) with hEq | hBad
  · have hErr0 : sacGateError204 (rss3ToSacGate x y r0 r1 deltaZ a b deltaC) = Fq204.zero := by
      unfold sacGateError204
      rw [hEq, Fq204.sub_eq_add_neg, Fq204.add_right_neg]
    rw [rss3ToSacGate_error_eq_delta] at hErr0
    exact False.elim (hCheat hErr0)
  · exact hBad

/-- Multi-turn execution of `rssSacrificedSignStep` across a trace of distributed attempts. -/
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
    let stNext := match out with
      | .ok st' _ => st'
      | .err st' _ => st'
    let tail := runRssSacrificedTrace chalHash sampleInBall stNext rest
    (tail.1, out :: tail.2)

/-- **Multi-Turn Distributed RSS Sacrifice Refinement (`rss_distributed_trace_refines_sacrificedSignStep`)**:
    Across any multi-turn signing trace `tr`:
    1. `nextAttempt` is monotonically non-decreasing (`st.nextAttempt ≤ stFinal.nextAttempt`);
    2. On every turn `(inp, chi, T)` in the trace, from any intermediate state `stCur`, either
       `rssSacrificedSignStep` equals the ideal `rssThresholdSignStep` transition, OR it aborts
       before opening with `.mpcSacrificeFailed` / `.attemptReplay`, OR `chi ∈ rssSacrificeBadChallenges204 T`. -/
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
    let stNext := match out with | .ok st' _ => st' | .err st' _ => st'
    have hStepMono : st.nextAttempt ≤ stNext.nextAttempt := by
      dsimp only [stNext, out]
      unfold rssSacrificedSignStep
      cases decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
      | false => exact Nat.le_refl _
      | true =>
        cases rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
        | false => dsimp only; omega
        | true =>
          unfold rssSignCore mkRssSignAttemptOutcome
          dsimp only
          split <;> dsimp only <;> omega
    obtain ⟨hTailMono, hTailRef⟩ := rss_distributed_trace_refines_sacrificedSignStep chalHash sampleInBall stNext rest
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
        | false =>
          left
          unfold rssThresholdSignStep
          rw [hg]
        | true =>
          right; left
          rw [hv]
          exact ⟨{ stCur with nextAttempt := stCur.nextAttempt + 1 }, rfl⟩
    · exact hTailRef turn hInRest stCur

/-- **`(t, n)` Custodian Subset-Key PRSS -> PRF Hybrid Reduction (`rss_prss_choose_hybrid`)**:
    In `(t, n)` replicated secret sharing (`Structure::new(n, t)` in `rss_mpc.rs`), there are
    `M = binomRec n (t - 1)` PRSS subset keys (`3` for `(2, 3)`, `5` for `(2, 5)`, `10` for `(3, 5)`).
    Replacing all `M` PRF-expanded mask tapes by independent uniform tapes changes any
    distinguisher's hit count by at most `M * (N ^ (M - 1) * ε)`. -/
theorem rss_prss_choose_hybrid {O : Type} {N : Nat} (real ideal : Fin N → O)
    (n t : Nat) (D : List O → Bool) (ε : Nat)
    (hPRF : PrssSingleKeyBound real ideal D ε) :
    let numKeys := binomRec n (t - 1)
    prssGap (prssRealHits real numKeys D) (prssIdealHits ideal numKeys D) ≤
      numKeys * (N ^ (numKeys - 1) * ε) :=
  prss_multi_key_hybrid real ideal (binomRec n (t - 1)) D ε hPRF

theorem rss_deployed_quorum_subset_counts :
    binomRec 3 (2 - 1) = 3 ∧
    binomRec 5 (2 - 1) = 5 ∧
    binomRec 5 (3 - 1) = 10 := by
  decide

theorem tooth_rss3_unverified_shift_corrupts_recon :
    let zeroSh : Rss3Share := ⟨Fq204.zero, Fq204.zero, Fq204.zero⟩
    rss3Recon (rss3MulStep zeroSh zeroSh Fq204.zero Fq204.zero Fq204.one) ≠
      Fq204.mul (rss3Recon zeroSh) (rss3Recon zeroSh) ∧
    sacAcceptRepeated [ext6Zero]
      (rss3ToSacGate zeroSh zeroSh Fq204.zero Fq204.zero Fq204.one ext6Zero zeroSh
        (ext6EmbedFq Fq204.one)) = false := by
  decide

theorem rss3_repeated_sacrifice_witness :
    ∃ (x y : Rss3Share) (r0 r1 deltaZ : Fq204)
      (a : Ext6Fq204) (b : Rss3Share) (deltaC : Ext6Fq204) (chis : List Ext6Fq204),
      deltaZ ≠ Fq204.zero ∧
      (sacAcceptRepeated chis (rss3ToSacGate x y r0 r1 deltaZ a b deltaC) = true →
        ∀ chi ∈ chis, chi = sacBadChallenge204 (rss3ToSacGate x y r0 r1 deltaZ a b deltaC)) ∧
      2 ^ 256 < mldsaQ ^ 12 := by
  let zSh : Rss3Share := ⟨Fq204.zero, Fq204.zero, Fq204.zero⟩
  have hNe : Fq204.one ≠ Fq204.zero := by decide
  exact ⟨zSh, zSh, Fq204.zero, Fq204.zero, Fq204.one, ext6Zero, zSh, ext6Zero, [ext6Zero],
    hNe, rss3_repeated_sacrifice_pq256 zSh zSh Fq204.zero Fq204.zero Fq204.one
      ext6Zero zSh ext6Zero [ext6Zero] hNe⟩

#tooth_pair mlDsa_all_three_levels_wellFormed vs tooth_mlDsaLevelWellFormed_bad_beta
#verify_inhabited mlDsa_challenge_entropy_bounds mlDsa_challenge_entropy_witness
#tooth_pair threshold_mldsa_abort_transcript_zk vs tooth_unsealed_w1_or_irwin_hall_abort_leaks_secret
#verify_inhabited threshold_mldsa_abort_transcript_zk threshold_mldsa_abort_zk_witness
#tooth_pair rss3_repeated_sacrifice_pq256 vs tooth_rss3_unverified_shift_corrupts_recon
#verify_inhabited rss3_repeated_sacrifice_pq256 rss3_repeated_sacrifice_witness

end Qsag

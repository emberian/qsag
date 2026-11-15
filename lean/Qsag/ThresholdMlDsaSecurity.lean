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

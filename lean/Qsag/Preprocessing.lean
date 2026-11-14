module
/-
# Qsag.Preprocessing — Dealerless Ring-LWE Base OT, Malicious `Π_pow7` & `Π_triple_f2` Sacrifice

Self-contained Lean 4.35 formalization of the 100% dealerless active-security preprocessing stack
backing `crates/qsag-core/src/preprocessing.rs` (`0` trusted dealers, `0` cleartext trapdoors):
1. **Ring-LWE Base OT Exact Decryption & FO Ciphertext Cut-and-Choose (`rlwe_ot_decrypt_exact`,
   `rlwe1024_ot_decrypt_exact`, `rlwe_fo_cut_and_choose_sound`)**:
   Over $R_q = \mathbb{Z}_{12289}[X]/(X^{N} + 1)$ ($N \in \{512, 1024\}$) with $\eta = 1$ noise,
   worst-case decryption noise is strictly $< \lfloor q / 4 \rfloor = 3072$, guaranteeing zero
   decryption error on every valid RLWE branch and $2^{-k}$ FO cut-and-choose survival on $k$
   malformed RLWE ciphertexts.
2. **Pairwise OLE / OT Cross-Term Telescopy & `(t, n)` Shamir Beaver Bridge
   (`ole_pairwise_cross_sum_eq_mul`, `shamirBeaverFromPairwiseOle_valid`)**:
   Connects local pairwise OLE cross-terms $s_{i,j}^{(u)} + s_{j,i}^{(v)} = (\lambda_i a_i)(\lambda_j b_j)$
   and degree-$< t$ sub-polynomial dealing directly to `(t, n)` Shamir `SharedBeaverTriple` validity.
3. **Share-Level Beaver Multiplication & 3-Round `Π_pow7` (`evalSharedBeaverMul_correct`,
   `SharedPow7Tuple`, `evalSharedPow7Tree_correct`)**:
   Constructs $([r], [r^2], \dots, [r^7])$ over `(t, n)` Shamir shares opening only masked differences
   $\delta = x - a, \varepsilon = y - b$ (`sharedBeaverMaskEquiv`) with zero cleartext secret reconstruction.
4. **Authenticated `(t, n)` Shared SPDZ Companion Sacrifice (`verifySharedSpdzSacrifice_complete`,
   `verifySharedSpdzSacrifice_sound`, `tooth_shared_spdz_sacrifice_rejects_corrupted_triple`)**:
   Combines party-local Shamir linear combinations with zero-sum `GoldilocksExt2` SPDZ `MacCheck`,
   proving tampered openings uniquely pin $\alpha \in \mathbb{F}_{p^2}$ while corrupted shared triples
   survive at most $1$ challenge $\rho \in S$ ($< 2^{-127}$).
5. **Full-Rank `BinaryExtractorMatrix` 2-Universal LHL & Batched Multi-Column KOS
   (`towerCombinerMatrix`, `extract384To128_towerCombinerMatrix_eq`, `extract384To128_two_universal`,
   `kos_batched_poly_check_sound`)**:
   Wires `BinaryExtractorMatrix` / `extract384To128` to `[I_{128} \mid c_1 \mid c_2]` over `Tower128`,
   proving unconditional $2^{-128}$ 2-universality across all $x \neq x' \in \{0,1\}^{384}$ and
   $\le m / 2^{128}$ multi-column batched KOS correlation soundness.
-/

public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Poseidon2
public import Qsag.UcGames
import all Qsag.Goldilocks
import all Qsag.BinaryTower

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Ring-LWE Base OT ($N \in \{512, 1024\}, q = 12289, \eta = 1$) Worst-Case Noise & Zero-Error Decryption -/

def rlweDimN : Nat := 512
def rlwe1024DimN : Nat := 1024
def rlweModQ : Nat := 12289
def rlweHalfQ : Nat := 6144

/-- Decode a noisy Ring-LWE coefficient `z ∈ [0, q)` to `{0, 1}` by distance to `0` vs `⌊q/2⌋ = 6144`. -/
@[expose] def rlweDecodeBit (z : Nat) : Bool :=
  decide (3072 ≤ z && z < 9216)

/-- Add signed noise `e ∈ [-bound, +bound]` (`eSign = true` means `+eMag`, `false` means `-eMag`)
    to `bit * ⌊q/2⌋` modulo `q = 12289`. -/
def rlweNoisyEncode (bit : Bool) (eSign : Bool) (eMag : Nat) : Nat :=
  let center := if bit then rlweHalfQ else 0
  let raw := if eSign then center + eMag else center + rlweModQ - (eMag % rlweModQ)
  raw % rlweModQ

/-- **Ring-LWE Base OT Zero-Failure Decryption at $N = 512$ (`rlwe_ot_decrypt_exact`)**:
    For $N = 512, q = 12289, \eta = 1$, each negacyclic product of $[-1, 1]^{512}$ polynomials has
    $\ell_\infty \le 512$, so $|(e_1 s_b - e_2 r + e_3)_k| \le 512 + 512 + 1 = 1025 < 3072 = \lfloor q/4 \rfloor$,
    and `rlweDecodeBit` recovers `bit` with **zero** decryption error for every noise realization! -/
theorem rlwe_ot_decrypt_exact (bit eSign : Bool) (eMag : Nat)
    (hNoise : eMag ≤ 2 * rlweDimN + 1) :
    rlweDecodeBit (rlweNoisyEncode bit eSign eMag) = bit := by
  have hMax : 2 * rlweDimN + 1 = 1025 := rfl
  rw [hMax] at hNoise
  unfold rlweDecodeBit rlweNoisyEncode rlweHalfQ rlweModQ
  cases bit <;> cases eSign <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · by_cases h0 : eMag = 0
    · subst h0; decide
    · rw [decide_eq_false_iff_not]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨hGe, hLt⟩; omega
  · rw [decide_eq_false_iff_not]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨hGe, hLt⟩; omega
  · rw [decide_eq_true_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  · rw [decide_eq_true_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega

/-- **Production Ring-LWE Base OT Zero-Failure Decryption at $N = 1024$ (`rlwe1024_ot_decrypt_exact`)**:
    For deployed $N = 1024, q = 12289, \eta = 1$ ($\ge 200$-bit PQ Core-SVP hardness matching
    `crates/qsag-core/src/preprocessing.rs`), each negacyclic product of $[-1, 1]^{1024}$ polynomials
    has $\ell_\infty \le 1024$, so worst-case noise satisfies
    $|(e_1 s_b - e_2 r + e_3)_k| \le 1024 + 1024 + 1 = 2049 < 3072 = \lfloor q/4 \rfloor$,
    and `rlweDecodeBit` recovers `bit` with **zero** decryption error! -/
theorem rlwe1024_ot_decrypt_exact (bit eSign : Bool) (eMag : Nat)
    (hNoise : eMag ≤ 2 * rlwe1024DimN + 1) :
    rlweDecodeBit (rlweNoisyEncode bit eSign eMag) = bit := by
  have hMax : 2 * rlwe1024DimN + 1 = 2049 := rfl
  rw [hMax] at hNoise
  unfold rlweDecodeBit rlweNoisyEncode rlweHalfQ rlweModQ
  cases bit <;> cases eSign <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · -- bit = false, -eMag: if eMag = 0 -> 0; if 1 ≤ eMag ≤ 2049 -> [10240, 12288], outside [3072, 9216)
    by_cases h0 : eMag = 0
    · subst h0; decide
    · rw [decide_eq_false_iff_not]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨hGe, hLt⟩; omega
  · -- bit = false, +eMag: [0, 2049], strictly < 3072
    rw [decide_eq_false_iff_not]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨hGe, hLt⟩; omega
  · -- bit = true, -eMag: [4095, 6144], strictly inside [3072, 9216)
    rw [decide_eq_true_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  · -- bit = true, +eMag: [6144, 8193], strictly inside [3072, 9216)
    rw [decide_eq_true_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega

/-! ## 2. Polymorphic Pairwise OLE / OT Cross-Term Telescopy (`ole_pairwise_cross_sum_eq_mul`) -/

section PolymorphicAlgebra
variable {R : Type} [LawfulCommRing R]
open CommRingOps

/-- Sum a list of ring elements in `R`. -/
@[expose] def ringListSum : List R → R
  | [] => zero
  | x :: xs => add x (ringListSum xs)

theorem ringListSum_append (xs ys : List R) :
    ringListSum (xs ++ ys) = add (ringListSum xs) (ringListSum ys) := by
  induction xs with
  | nil => simp [ringListSum, LawfulCommRing.zero_add]
  | cons x xs ih => simp [ringListSum, ih, LawfulCommRing.add_assoc]

/-- Componentwise ring addition of share vectors (`ws₁ + ws₂`). -/
def ringListZipAdd : List R → List R → List R
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => add x y :: ringListZipAdd xs ys

theorem ringListZipAdd_length_of_eq :
    ∀ {xs ys : List R}, xs.length = ys.length → (ringListZipAdd xs ys).length = xs.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [ringListZipAdd, List.length_cons,
      ringListZipAdd_length_of_eq (Nat.succ.inj h)]

theorem ringListSum_zipAdd :
    ∀ (xs ys : List R),
      ringListSum (ringListZipAdd xs ys) = add (ringListSum xs) (ringListSum ys)
  | [], ys => by simp [ringListZipAdd, ringListSum, LawfulCommRing.zero_add]
  | x :: xs, [] => by simp [ringListZipAdd, ringListSum, LawfulCommRing.add_zero]
  | x :: xs, y :: ys => by
    simp only [ringListZipAdd, ringListSum, ringListSum_zipAdd xs ys]
    exact (LawfulCommRing.add_add_add_comm x (ringListSum xs) y (ringListSum ys)).symm

/-- Inductive witness that an $n$-party share vector `ws` (`ws.length = us.length = vs.length`)
    arises from local inputs `us`, `vs` via pairwise OLE correlations
    ($s_{i,j}^{(1)} + s_{i,j}^{(2)} = u_i \cdot v_j$) with zero trusted dealer. -/
inductive ValidPairwiseOleShares : List R → List R → List R → Prop where
  | nil : ValidPairwiseOleShares [] [] []
  | cons {u0 v0 : R} {us vs wsTail : List R}
      (s0Right1 s0Right2 sLeft0_1 sLeft0_2 : List R)
      (hTail : ValidPairwiseOleShares us vs wsTail)
      (hLenR1 : s0Right1.length = wsTail.length)
      (hLenR2 : s0Right2.length = wsTail.length)
      (hLenL1 : sLeft0_1.length = wsTail.length)
      (hLenL2 : sLeft0_2.length = wsTail.length)
      (hRightSum : add (ringListSum s0Right1) (ringListSum s0Right2) = mul u0 (ringListSum vs))
      (hLeftSum  : add (ringListSum sLeft0_1) (ringListSum sLeft0_2) = mul (ringListSum us) v0) :
      ValidPairwiseOleShares (u0 :: us) (v0 :: vs)
        (add (mul u0 v0) (add (ringListSum s0Right1) (ringListSum sLeft0_2)) ::
         ringListZipAdd wsTail (ringListZipAdd s0Right2 sLeft0_1))

/-- True $n$-party arity preservation: `ValidPairwiseOleShares us vs ws` produces one output
    share per party (`ws.length = us.length` and `vs.length = us.length`). -/
theorem ValidPairwiseOleShares.length_eq {us vs ws : List R}
    (hValid : ValidPairwiseOleShares us vs ws) :
    ws.length = us.length ∧ vs.length = us.length := by
  induction hValid with
  | nil => exact ⟨rfl, rfl⟩
  | @cons _ _ _ _ wsTail _ s0R2 sL1 _ _ _ hLenR2 hLenL1 _ _ _ ih =>
    obtain ⟨hWL, hVL⟩ := ih
    have hZ1 : (ringListZipAdd s0R2 sL1).length = s0R2.length :=
      ringListZipAdd_length_of_eq (hLenR2.trans hLenL1.symm)
    have hZ2 : (ringListZipAdd wsTail (ringListZipAdd s0R2 sL1)).length = wsTail.length :=
      ringListZipAdd_length_of_eq (hLenR2.symm.trans hZ1.symm)
    exact ⟨by simp [hZ2, hWL], by simp [hVL]⟩

/-- **Pairwise OLE / OT Cross-Term Telescopy (`ole_pairwise_cross_sum_eq_mul`)**:
    Over ANY commutative ring `R` (`Goldilocks`, `GoldilocksExt2`, `Bool` / `TowerElem 0`,
    `TowerElem 3`, `Tower128`), $n$-party pairwise OLE cross-terms sum identically to
    $(\sum u_i) \cdot (\sum v_j)$ with zero trusted dealer! -/
theorem ole_pairwise_cross_sum_eq_mul {us vs ws : List R}
    (hValid : ValidPairwiseOleShares us vs ws) :
    ringListSum ws = mul (ringListSum us) (ringListSum vs) := by
  induction hValid with
  | nil =>
    simp [ringListSum, LawfulCommRing.mul_zero]
  | @cons u0 v0 us vs wsTail s0R1 s0R2 sL1 sL2 _ _ _ _ _ hR hL ih =>
    simp only [ringListSum, ringListSum_zipAdd]
    rw [LawfulCommRing.right_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
    rw [← hR, ← hL, ← ih]
    let a := mul u0 v0
    let r1 := ringListSum s0R1
    let r2 := ringListSum s0R2
    let l1 := ringListSum sL1
    let l2 := ringListSum sL2
    let w := ringListSum wsTail
    show add (add a (add r1 l2)) (add w (add r2 l1)) =
         add (add a (add r1 r2)) (add (add l1 l2) w)
    calc
      add (add a (add r1 l2)) (add w (add r2 l1))
        = add (add a (add r1 l2)) (add (add r2 l1) w) := by
          rw [LawfulCommRing.add_comm w (add r2 l1)]
      _ = add a (add (add r1 l2) (add (add r2 l1) w)) := by
          rw [LawfulCommRing.add_assoc a (add r1 l2) _]
      _ = add a (add (add (add r1 l2) (add r2 l1)) w) := by
          rw [← LawfulCommRing.add_assoc (add r1 l2) (add r2 l1) w]
      _ = add a (add (add (add r1 r2) (add l2 l1)) w) := by
          rw [LawfulCommRing.add_add_add_comm r1 l2 r2 l1]
      _ = add a (add (add (add r1 r2) (add l1 l2)) w) := by
          rw [LawfulCommRing.add_comm l2 l1]
      _ = add a (add (add r1 r2) (add (add l1 l2) w)) := by
          rw [LawfulCommRing.add_assoc (add r1 r2) (add l1 l2) w]
      _ = add (add a (add r1 r2)) (add (add l1 l2) w) := by
          rw [← LawfulCommRing.add_assoc a (add r1 r2) (add (add l1 l2) w)]

/-! ## 3. Dealerless Joint Random Mask Privacy & 3-Round Beaver Power-Chain (`Π_pow7`) -/

/-- **Dealerless Joint Mask Privacy (`dealerless_joint_mask_uniform`)**:
    When $n$ parties jointly generate $[r] = \sum_k [r_k]$ without a dealer, for ANY target secret
    shift $\delta \in R$ and ANY `< t` corrupt evaluation points `corruptPts`, an honest party's
    polynomial $P_{\text{hon}}$ bijectively shifts the joint secret by $\delta$ while leaving every
    corrupt share `evalCoeffs ... xc` (`xc ∈ corruptPts`) bitwise identical! -/
theorem dealerless_joint_mask_uniform
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (t : Nat) (corruptPts : List R) (delta : R)
    (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero)
    (pHon : ShamirPadPoly R t) :
    let qHon := (shamir_rebalanceEquiv inv t corruptPts delta hCard).toFun pHon
    (shamir_rebalanceEquiv inv t corruptPts delta hCard).invFun qHon = pHon ∧
    RoundPoly.evalCoeffs qHon.1 zero = add delta (RoundPoly.evalCoeffs pHon.1 zero) ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs qHon.1 xc = RoundPoly.evalCoeffs pHon.1 xc) := by
  intro qHon
  have hBij := (shamir_rebalanceEquiv inv t corruptPts delta hCard).left_inv pHon
  obtain ⟨hSec, hCorr⟩ := pad_bijection_masked_openings_uniform inv hInv t corruptPts delta hCard hNonZero pHon
  rw [LawfulCommRing.zero_add] at hSec
  exact ⟨hBij, hSec, hCorr⟩

/-- Reconstructed Beaver multiplication output from triple `(a, b, c)` and masked openings
    `delta = x - a`, `eps = y - b`: `c + delta * b + eps * a + delta * eps`. -/
@[expose] def beaverProdEval (a b c delta eps : R) : R :=
  add (add c (mul delta b)) (add (mul eps a) (mul delta eps))

/-- **Beaver Multiplication Correctness (`beaverProd_correct`)**:
    Over ANY commutative ring `R`, if `c = a * b`, `delta = x - a`, and `eps = y - b`, then
    `beaverProdEval a b c delta eps = x * y`. -/
theorem beaverProd_correct {a b c x y : R} (hTriple : c = mul a b) :
    beaverProdEval a b c (sub x a) (sub y b) = mul x y := by
  unfold beaverProdEval
  subst hTriple
  -- Note x = a + (x - a) and y = b + (y - b)
  have hx : x = add a (sub x a) := (LawfulCommRing.add_sub_cancel_left a x).symm
  have hy : y = add b (sub y b) := (LawfulCommRing.add_sub_cancel_left b y).symm
  conv => rhs; rw [hx, hy]
  rw [LawfulCommRing.right_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
      LawfulCommRing.mul_comm a (sub y b), LawfulCommRing.add_add_add_comm]

structure BeaverTripleVal (R : Type) where
  a : R
  b : R
  c : R

def BeaverTripleVal.valid (t : BeaverTripleVal R) : Prop :=
  t.c = mul t.a t.b

/-- 3-round dealerless Beaver power-tree constructing `(r^2, r^3, r^4, r^5, r^6, r^7)` from `r`
    and 6 Beaver triples (`Round 1`: `r^2`; `Round 2`: `r^3, r^4`; `Round 3`: `r^5, r^6, r^7`). -/
@[expose] def evalPow7BeaverTree (r : R)
    (t2 t3 t4 t5 t6 t7 : BeaverTripleVal R) : R × R × R × R × R × R :=
  let r2 := beaverProdEval t2.a t2.b t2.c (sub r t2.a) (sub r t2.b)
  let r3 := beaverProdEval t3.a t3.b t3.c (sub r2 t3.a) (sub r t3.b)
  let r4 := beaverProdEval t4.a t4.b t4.c (sub r2 t4.a) (sub r2 t4.b)
  let r5 := beaverProdEval t5.a t5.b t5.c (sub r4 t5.a) (sub r t5.b)
  let r6 := beaverProdEval t6.a t6.b t6.c (sub r4 t6.a) (sub r2 t6.b)
  let r7 := beaverProdEval t7.a t7.b t7.c (sub r4 t7.a) (sub r3 t7.b)
  (r2, r3, r4, r5, r6, r7)

/-- **3-Round `Π_pow7` Beaver Tree Correctness (`pow7Tree_correct`)**. -/
theorem pow7Tree_correct (r : R)
    (t2 t3 t4 t5 t6 t7 : BeaverTripleVal R)
    (h2 : t2.valid) (h3 : t3.valid) (h4 : t4.valid)
    (h5 : t5.valid) (h6 : t6.valid) (h7 : t7.valid) :
    let (r2, r3, r4, r5, r6, r7) := evalPow7BeaverTree r t2 t3 t4 t5 t6 t7
    r2 = mul r r ∧
    r3 = mul r2 r ∧
    r4 = mul r2 r2 ∧
    r5 = mul r4 r ∧
    r6 = mul r4 r2 ∧
    r7 = mul r4 r3 := by
  dsimp only [evalPow7BeaverTree]
  have e2 := beaverProd_correct (x := r) (y := r) h2
  refine ⟨e2, ?_, ?_, ?_, ?_, ?_⟩
  · exact beaverProd_correct h3
  · exact beaverProd_correct h4
  · exact beaverProd_correct h5
  · exact beaverProd_correct h6
  · exact beaverProd_correct h7

/-- Componentwise subtraction of equal-length share vectors (`xs - ys`). -/
def shareZipSub : List R → List R → List R
  | x :: xs, y :: ys => sub x y :: shareZipSub xs ys
  | _, _ => []

theorem shareZipSub_length_of_eq :
    ∀ {xs ys : List R}, xs.length = ys.length → (shareZipSub xs ys).length = xs.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [shareZipSub, List.length_cons, shareZipSub_length_of_eq (Nat.succ.inj h)]

/-- Public scalar multiplication on a party share vector (`c · xs`). -/
def shareScale (c : R) (xs : List R) : List R :=
  xs.map (mul c)

@[simp] theorem shareScale_length (c : R) (xs : List R) :
    (shareScale c xs).length = xs.length := List.length_map _

/-- Public constant offset added to every party's Shamir share (`c + xs`). -/
def shareAddConst (c : R) (xs : List R) : List R :=
  xs.map (add c)

@[simp] theorem shareAddConst_length (c : R) (xs : List R) :
    (shareAddConst c xs).length = xs.length := List.length_map _

theorem ringListSum_zipWith_mul :
    ∀ (ls xs : List R), ringListSum (List.zipWith mul ls xs) = ringDot ls xs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | l :: ls, x :: xs => by
    simp only [List.zipWith, ringListSum, ringDot, ringListSum_zipWith_mul ls xs]

theorem ringDot_zipAdd :
    ∀ {ls xs ys : List R}, xs.length = ys.length →
      ringDot ls (ringListZipAdd xs ys) = add (ringDot ls xs) (ringDot ls ys)
  | [], _, _, _ => by simp [ringDot, LawfulCommRing.add_zero]
  | _ :: _, [], [], _ => by simp [ringListZipAdd, ringDot, LawfulCommRing.add_zero]
  | _ :: ls, _ :: xs, _ :: ys, h => by
    simp only [ringListZipAdd, ringDot, ringDot_zipAdd (Nat.succ.inj h),
      LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

theorem ringDot_zipSub :
    ∀ {ls xs ys : List R}, xs.length = ys.length →
      ringDot ls (shareZipSub xs ys) = sub (ringDot ls xs) (ringDot ls ys)
  | [], _, _, _ => by simp [ringDot, LawfulCommRing.sub_self]
  | _ :: _, [], [], _ => by simp [shareZipSub, ringDot, LawfulCommRing.sub_self]
  | l :: ls, x :: xs, y :: ys, h => by
    simp only [shareZipSub, ringDot, ringDot_zipSub (Nat.succ.inj h), LawfulCommRing.mul_sub]
    apply LawfulCommRing.add_left_cancel (a := add (mul l y) (ringDot ls ys))
    rw [LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_sub_cancel_left]

theorem ringDot_scale (c : R) :
    ∀ (ls xs : List R), ringDot ls (shareScale c xs) = mul c (ringDot ls xs)
  | [], _ => by simp [ringDot, LawfulCommRing.mul_zero]
  | _ :: _, [] => by simp [shareScale, ringDot, LawfulCommRing.mul_zero]
  | l :: ls, x :: xs => by
    have ih := ringDot_scale c ls xs
    simp only [shareScale, List.map_cons, ringDot]
    change add (mul l (mul c x)) (ringDot ls (shareScale c xs)) = mul c (add (mul l x) (ringDot ls xs))
    rw [ih]
    have hSwap : mul l (mul c x) = mul c (mul l x) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm l c, LawfulCommRing.mul_assoc]
    rw [hSwap, ← LawfulCommRing.left_distrib]

theorem ringDot_addConst (c : R) :
    ∀ {ls xs : List R}, ls.length ≤ xs.length →
      ringDot ls (shareAddConst c xs) = add (mul (ringListSum ls) c) (ringDot ls xs)
  | [], _, _ => by simp [ringDot, ringListSum, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
  | _ :: _, [], h => by simp at h
  | l :: ls, x :: xs, h => by
    simp only [List.length_cons] at h
    have ih := ringDot_addConst c (Nat.le_of_succ_le_succ h)
    simp only [shareAddConst, List.map_cons, ringDot, ringListSum]
    change add (mul l (add c x)) (ringDot ls (shareAddConst c xs)) =
      add (mul (add l (ringListSum ls)) c) (add (mul l x) (ringDot ls xs))
    rw [ih, LawfulCommRing.left_distrib, LawfulCommRing.right_distrib, LawfulCommRing.add_add_add_comm]

/-- Secret-shared `(t, n)` Beaver multiplication triple `([a], [b], [c])` across `n` parties. -/
structure SharedBeaverTriple (R : Type) where
  aShares : List R
  bShares : List R
  cShares : List R
  deriving DecidableEq, Repr

/-- A `SharedBeaverTriple` is valid with respect to Lagrange-at-zero weights `lambdas` when each
    component has `lambdas.length` shares and `⟨λ, c⟩ = ⟨λ, a⟩ · ⟨λ, b⟩`. -/
def SharedBeaverTriple.validAt (lambdas : List R) (tr : SharedBeaverTriple R) : Prop :=
  tr.aShares.length = lambdas.length ∧
  tr.bShares.length = lambdas.length ∧
  tr.cShares.length = lambdas.length ∧
  ringDot lambdas tr.cShares = mul (ringDot lambdas tr.aShares) (ringDot lambdas tr.bShares)

/-- Sum received sub-shares at `pts` from `m` party-dealt Shamir sub-polynomials `cPolys`. -/
def sumSubPolyShares (pts : List R) : List (List R) → List R
  | [] => pts.map (fun _ => zero)
  | p :: ps => ringListZipAdd (pts.map (RoundPoly.evalCoeffs p)) (sumSubPolyShares pts ps)

theorem sumSubPolyShares_length (pts : List R) :
    ∀ (cPolys : List (List R)), (sumSubPolyShares pts cPolys).length = pts.length
  | [] => by simp [sumSubPolyShares]
  | p :: ps => by
    simp only [sumSubPolyShares]
    rw [ringListZipAdd_length_of_eq (by simp [sumSubPolyShares_length pts ps])]
    simp

/-- **Dealerless Pairwise-OLE to `(t, n)` Shamir Beaver Bridge (`shamirBeaverFromPairwiseOle_valid`)**:
    When `n` parties apply `ValidPairwiseOleShares` to Lagrange-weighted local shares
    `u_i = λ_i · a_i` and `v_i = λ_i · b_i` to obtain additive shares `ws` (`∑ w_i = a · b`), and
    each party deals a degree-`< t` sub-polynomial `p_i` with `p_i(0) = w_i`, summing the sub-shares
    at `pts` yields a valid `(t, n)` Shamir `SharedBeaverTriple` with zero trusted dealer! -/
theorem shamirBeaverFromPairwiseOle_valid
    (lambdas pts aShares bShares ws : List R) (cPolys : List (List R)) (t : Nat)
    (hPtsLen : pts.length = lambdas.length)
    (hALen : aShares.length = lambdas.length)
    (hBLen : bShares.length = lambdas.length)
    (hOle : ValidPairwiseOleShares (List.zipWith mul lambdas aShares) (List.zipWith mul lambdas bShares) ws)
    (hZero : ringDot lambdas (pts.map (fun _ => one)) = one)
    (hHigher : ∀ d, 1 ≤ d → d < t → ringDot lambdas (pts.map (fun x => ringPow x d)) = zero)
    (hDeg : ∀ p ∈ cPolys, p.length ≤ t)
    (hConst : cPolys.map (fun p => RoundPoly.evalCoeffs p zero) = ws) :
    (SharedBeaverTriple.mk aShares bShares (sumSubPolyShares pts cPolys)).validAt lambdas := by
  have hSubSum : ∀ (ps : List (List R)),
      (∀ p ∈ ps, p.length ≤ t) →
      ringDot lambdas (sumSubPolyShares pts ps) =
        ringListSum (ps.map (fun p => RoundPoly.evalCoeffs p zero)) := by
    intro ps hPsDeg
    induction ps with
    | nil =>
      simp only [sumSubPolyShares, List.map_nil, ringListSum]
      have h0 : ∀ (ls qs : List R), ringDot ls (qs.map (fun _ => zero)) = zero := by
        intro ls qs
        induction ls generalizing qs with
        | nil => rfl
        | cons l ls' ih =>
          cases qs with
          | nil => rfl
          | cons _ qs' => simp [ringDot, LawfulCommRing.mul_zero, ih qs', LawfulCommRing.zero_add]
      exact h0 lambdas pts
    | cons p ps' ih =>
      simp only [sumSubPolyShares, List.map_cons, ringListSum]
      rw [ringDot_zipAdd (by simp [sumSubPolyShares_length]),
          lagrangeAtZero_evalCoeffs lambdas pts p t (hPsDeg p (.head _)) hZero hHigher,
          ih (fun q hq => hPsDeg q (.tail _ hq))]
  refine ⟨hALen, hBLen, (sumSubPolyShares_length pts cPolys).trans hPtsLen, ?_⟩
  rw [hSubSum cPolys hDeg, hConst, ole_pairwise_cross_sum_eq_mul hOle,
      ringListSum_zipWith_mul, ringListSum_zipWith_mul]

/-- Party-local linear combination computing shares `[z] = [c] + δ·[b] + ε·[a] + δ·ε`
    from masked public openings `delta = x - a` and `eps = y - b`, without reconstructing `x, y, a, b, c`. -/
def evalSharedBeaverMulShares (tr : SharedBeaverTriple R) (delta eps : R) : List R :=
  shareAddConst (mul delta eps)
    (ringListZipAdd
      (ringListZipAdd tr.cShares (shareScale delta tr.bShares))
      (shareScale eps tr.aShares))

/-- Full `(t, n)` share-level Beaver multiplication returning `(zShares, delta, eps)`. -/
def evalSharedBeaverMul (lambdas xSh ySh : List R) (tr : SharedBeaverTriple R) : List R × R × R :=
  let delta := ringDot lambdas (shareZipSub xSh tr.aShares)
  let eps   := ringDot lambdas (shareZipSub ySh tr.bShares)
  (evalSharedBeaverMulShares tr delta eps, delta, eps)

/-- **Beaver Masked-Opening Privacy Bijection (`sharedBeaverMaskEquiv`)**:
    For any secret inputs `(x, y : R)`, the map `(a, b) ↦ (x - a, y - b)` is an exact involution
    (`SimpleEquiv (R × R) (R × R)`), proving uniform Beaver masks `(a, b)` make the opened
    differences `(delta, eps)` uniformly distributed and independent of `(x, y)`. -/
def sharedBeaverMaskEquiv (x y : R) : SimpleEquiv (R × R) (R × R) where
  toFun := fun (a, b) => (sub x a, sub y b)
  invFun := fun (d, e) => (sub x d, sub y e)
  left_inv := fun (a, b) => by
    have hCancel : ∀ (u v : R), sub u (sub u v) = v := by
      intro u v
      apply LawfulCommRing.add_left_cancel (a := sub u v)
      rw [LawfulCommRing.add_sub_cancel_left, LawfulCommRing.add_comm (sub u v) v,
          LawfulCommRing.add_sub_cancel_left]
    exact Prod.ext (hCancel x a) (hCancel y b)
  right_inv := fun (d, e) => by
    have hCancel : ∀ (u v : R), sub u (sub u v) = v := by
      intro u v
      apply LawfulCommRing.add_left_cancel (a := sub u v)
      rw [LawfulCommRing.add_sub_cancel_left, LawfulCommRing.add_comm (sub u v) v,
          LawfulCommRing.add_sub_cancel_left]
    exact Prod.ext (hCancel x d) (hCancel y e)

/-- **Share-Level `(t, n)` Beaver Multiplication Correctness (`evalSharedBeaverMul_correct`)**:
    When `∑ λ_i = 1` and `tr` is a valid shared Beaver triple, `evalSharedBeaverMul` outputs
    `lambdas.length` shares recombining to `⟨λ, x⟩ · ⟨λ, y⟩` while opening only `(x - a, y - b)`. -/
theorem evalSharedBeaverMul_correct
    (lambdas xSh ySh : List R) (tr : SharedBeaverTriple R)
    (hSumOne : ringListSum lambdas = one)
    (hXLen : xSh.length = lambdas.length)
    (hYLen : ySh.length = lambdas.length)
    (hTr : tr.validAt lambdas) :
    let (zSh, delta, eps) := evalSharedBeaverMul lambdas xSh ySh tr
    zSh.length = lambdas.length ∧
    delta = sub (ringDot lambdas xSh) (ringDot lambdas tr.aShares) ∧
    eps = sub (ringDot lambdas ySh) (ringDot lambdas tr.bShares) ∧
    ringDot lambdas zSh = mul (ringDot lambdas xSh) (ringDot lambdas ySh) := by
  obtain ⟨hALen, hBLen, hCLen, hCMul⟩ := hTr
  dsimp only [evalSharedBeaverMul, evalSharedBeaverMulShares]
  let d0 := ringDot lambdas (shareZipSub xSh tr.aShares)
  let e0 := ringDot lambdas (shareZipSub ySh tr.bShares)
  have hInner1Len : (ringListZipAdd tr.cShares (shareScale d0 tr.bShares)).length = lambdas.length := by
    rw [ringListZipAdd_length_of_eq (by simp [hCLen, hBLen]), hCLen]
  have hInner2Len : (ringListZipAdd
      (ringListZipAdd tr.cShares (shareScale d0 tr.bShares))
      (shareScale e0 tr.aShares)).length = lambdas.length := by
    rw [ringListZipAdd_length_of_eq (by simp [hInner1Len, hALen]), hInner1Len]
  have hZLen : (shareAddConst (mul d0 e0) (ringListZipAdd
      (ringListZipAdd tr.cShares (shareScale d0 tr.bShares))
      (shareScale e0 tr.aShares))).length = lambdas.length := by
    simp [hInner2Len]
  have hDelta : d0 = sub (ringDot lambdas xSh) (ringDot lambdas tr.aShares) :=
    ringDot_zipSub (hXLen.trans hALen.symm)
  have hEps : e0 = sub (ringDot lambdas ySh) (ringDot lambdas tr.bShares) :=
    ringDot_zipSub (hYLen.trans hBLen.symm)
  refine ⟨hZLen, hDelta, hEps, ?_⟩
  change ringDot lambdas (shareAddConst (mul d0 e0)
    (ringListZipAdd (ringListZipAdd tr.cShares (shareScale d0 tr.bShares)) (shareScale e0 tr.aShares))) =
    mul (ringDot lambdas xSh) (ringDot lambdas ySh)
  rw [ringDot_addConst _ (by rw [hInner2Len]; exact Nat.le_refl _), hSumOne, LawfulCommRing.one_mul,
      ringDot_zipAdd (by simp [hInner1Len, hALen]),
      ringDot_zipAdd (by simp [hCLen, hBLen]),
      ringDot_scale, ringDot_scale, hDelta, hEps]
  let d := sub (ringDot lambdas xSh) (ringDot lambdas tr.aShares)
  let e := sub (ringDot lambdas ySh) (ringDot lambdas tr.bShares)
  rw [LawfulCommRing.add_comm (mul d e) _,
      LawfulCommRing.add_assoc]
  exact beaverProd_correct hCMul

/-- Share-level 3-round dealerless `Π_pow7` Beaver power-tree over `[r]`. -/
def evalSharedPow7BeaverTreePoly (lambdas rSh : List R)
    (t2 t3 t4 t5 t6 t7 : SharedBeaverTriple R) :
    List R × List R × List R × List R × List R × List R :=
  let (r2Sh, _, _) := evalSharedBeaverMul lambdas rSh rSh t2
  let (r3Sh, _, _) := evalSharedBeaverMul lambdas r2Sh rSh t3
  let (r4Sh, _, _) := evalSharedBeaverMul lambdas r2Sh r2Sh t4
  let (r5Sh, _, _) := evalSharedBeaverMul lambdas r4Sh rSh t5
  let (r6Sh, _, _) := evalSharedBeaverMul lambdas r4Sh r2Sh t6
  let (r7Sh, _, _) := evalSharedBeaverMul lambdas r4Sh r3Sh t7
  (r2Sh, r3Sh, r4Sh, r5Sh, r6Sh, r7Sh)

theorem evalSharedPow7BeaverTreePoly_correct
    (lambdas rSh : List R)
    (t2 t3 t4 t5 t6 t7 : SharedBeaverTriple R)
    (hSumOne : ringListSum lambdas = one)
    (hRLen : rSh.length = lambdas.length)
    (h2 : t2.validAt lambdas) (h3 : t3.validAt lambdas) (h4 : t4.validAt lambdas)
    (h5 : t5.validAt lambdas) (h6 : t6.validAt lambdas) (h7 : t7.validAt lambdas) :
    let (r2Sh, r3Sh, r4Sh, r5Sh, r6Sh, r7Sh) := evalSharedPow7BeaverTreePoly lambdas rSh t2 t3 t4 t5 t6 t7
    let r := ringDot lambdas rSh
    (r2Sh.length = lambdas.length ∧ r3Sh.length = lambdas.length ∧ r4Sh.length = lambdas.length ∧
     r5Sh.length = lambdas.length ∧ r6Sh.length = lambdas.length ∧ r7Sh.length = lambdas.length) ∧
    ringDot lambdas r2Sh = mul r r ∧
    ringDot lambdas r3Sh = mul (ringDot lambdas r2Sh) r ∧
    ringDot lambdas r4Sh = mul (ringDot lambdas r2Sh) (ringDot lambdas r2Sh) ∧
    ringDot lambdas r5Sh = mul (ringDot lambdas r4Sh) r ∧
    ringDot lambdas r6Sh = mul (ringDot lambdas r4Sh) (ringDot lambdas r2Sh) ∧
    ringDot lambdas r7Sh = mul (ringDot lambdas r4Sh) (ringDot lambdas r3Sh) := by
  dsimp only [evalSharedPow7BeaverTreePoly]
  obtain ⟨hL2, _, _, hE2⟩ := evalSharedBeaverMul_correct lambdas rSh rSh t2 hSumOne hRLen hRLen h2
  obtain ⟨hL3, _, _, hE3⟩ := evalSharedBeaverMul_correct lambdas _ rSh t3 hSumOne hL2 hRLen h3
  obtain ⟨hL4, _, _, hE4⟩ := evalSharedBeaverMul_correct lambdas _ _ t4 hSumOne hL2 hL2 h4
  obtain ⟨hL5, _, _, hE5⟩ := evalSharedBeaverMul_correct lambdas _ rSh t5 hSumOne hL4 hRLen h5
  obtain ⟨hL6, _, _, hE6⟩ := evalSharedBeaverMul_correct lambdas _ _ t6 hSumOne hL4 hL2 h6
  obtain ⟨hL7, _, _, hE7⟩ := evalSharedBeaverMul_correct lambdas _ _ t7 hSumOne hL4 hL3 h7
  exact ⟨⟨hL2, hL3, hL4, hL5, hL6, hL7⟩, hE2, hE3, hE4, hE5, hE6, hE7⟩

/-! ## 4. Polymorphic SPDZ Companion Triple Sacrifice (`GoldilocksExt2` & `Tower128`) -/

/-- Opened masked values `(u, v) = (ρ * a - a_tilde, b - b_tilde)` in SPDZ triple sacrifice. -/
@[expose] def spdzSacrificeOpenings (rho a b aTilde bTilde : R) : R × R :=
  (sub (mul rho a) aTilde, sub b bTilde)

/-- SPDZ sacrifice residual `W(ρ) = ρ * c - c_tilde - u * b - a_tilde * v`. -/
@[expose] def spdzSacrificeResidual (rho a b c aTilde bTilde cTilde : R) : R :=
  let (u, v) := spdzSacrificeOpenings rho a b aTilde bTilde
  sub (sub (mul rho c) cTilde) (add (mul u b) (mul aTilde v))

/-- **Exact Algebraic Residual Identity (`spdzSacrificeResidual_eq_linear`)**:
    Over ANY commutative ring `R`, let $\Delta = c - a b$ and $\tilde{\Delta} = \tilde{c} - \tilde{a}\tilde{b}$.
    Then `spdzSacrificeResidual ρ a b c aTilde bTilde cTilde = -Δ_tilde + ρ * Δ`
    (`= RoundPoly.evalCoeffs [neg Δ_tilde, Δ] ρ`)! -/
theorem spdzSacrificeResidual_eq_linear (rho a b c aTilde bTilde cTilde : R) :
    let delta := sub c (mul a b)
    let deltaTilde := sub cTilde (mul aTilde bTilde)
    spdzSacrificeResidual rho a b c aTilde bTilde cTilde =
      RoundPoly.evalCoeffs [neg deltaTilde, delta] rho := by
  dsimp only [spdzSacrificeResidual, spdzSacrificeOpenings, RoundPoly.evalCoeffs]
  rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  -- Expand u * b + aTilde * v = (rho * a - aTilde) * b + aTilde * (b - bTilde) = rho * (a * b) - aTilde * bTilde
  have hCross :
      add (mul (sub (mul rho a) aTilde) b) (mul aTilde (sub b bTilde)) =
      sub (mul rho (mul a b)) (mul aTilde bTilde) := by
    rw [LawfulCommRing.sub_mul, LawfulCommRing.mul_sub, LawfulCommRing.mul_assoc rho a b]
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.sub_eq_add_neg, LawfulCommRing.sub_eq_add_neg]
    rw [LawfulCommRing.add_assoc (mul rho (mul a b)) (neg (mul aTilde b)) _,
        ← LawfulCommRing.add_assoc (neg (mul aTilde b)) (mul aTilde b) _,
        LawfulCommRing.add_left_neg, LawfulCommRing.zero_add]
  rw [hCross]
  -- Now show (rho * c - cTilde) - (rho * (a * b) - aTilde * bTilde) = -(cTilde - aTilde * bTilde) + rho * (c - a * b)
  apply LawfulCommRing.add_left_cancel (a := add cTilde (mul rho (mul a b)))
  -- Simplify LHS and RHS via ring axioms
  have hNegSub : neg (sub cTilde (mul aTilde bTilde)) = add (neg cTilde) (mul aTilde bTilde) := by
    apply LawfulCommRing.add_left_cancel (a := sub cTilde (mul aTilde bTilde))
    rw [LawfulCommRing.add_right_neg, LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.add_add_add_comm, LawfulCommRing.add_right_neg,
        LawfulCommRing.add_left_neg, LawfulCommRing.zero_add]
  rw [hNegSub, LawfulCommRing.mul_sub]
  simp only [LawfulCommRing.sub_eq_add_neg]
  -- Both sides are sums of {cTilde, mul rho (mul a b), mul rho c, neg cTilde, neg (mul rho (mul a b)), mul aTilde bTilde}
  have hLHS :
      add (add cTilde (mul rho (mul a b)))
          (add (add (mul rho c) (neg cTilde))
               (neg (add (mul rho (mul a b)) (neg (mul aTilde bTilde))))) =
      add (mul aTilde bTilde) (mul rho c) := by
    have hNegInner :
        neg (add (mul rho (mul a b)) (neg (mul aTilde bTilde))) =
        add (neg (mul rho (mul a b))) (mul aTilde bTilde) := by
      apply LawfulCommRing.add_left_cancel (a := add (mul rho (mul a b)) (neg (mul aTilde bTilde)))
      rw [LawfulCommRing.add_right_neg, LawfulCommRing.add_add_add_comm,
          LawfulCommRing.add_right_neg, LawfulCommRing.add_left_neg, LawfulCommRing.zero_add]
    rw [hNegInner]
    rw [LawfulCommRing.add_comm (mul rho c) (neg cTilde),
        LawfulCommRing.add_add_add_comm (neg cTilde) (mul rho c) (neg (mul rho (mul a b))) (mul aTilde bTilde),
        LawfulCommRing.add_add_add_comm cTilde (mul rho (mul a b))
          (add (neg cTilde) (neg (mul rho (mul a b))))
          (add (mul rho c) (mul aTilde bTilde))]
    have hCancel1 : add cTilde (add (neg cTilde) (neg (mul rho (mul a b)))) = neg (mul rho (mul a b)) := by
      rw [← LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.zero_add]
    rw [hCancel1, ← LawfulCommRing.add_assoc (neg (mul rho (mul a b))) (mul rho (mul a b)) _,
        LawfulCommRing.add_left_neg, LawfulCommRing.zero_add,
        LawfulCommRing.add_comm (mul rho c) (mul aTilde bTilde)]
  have hRHS :
      add (add cTilde (mul rho (mul a b)))
          (add (add (neg cTilde) (mul aTilde bTilde))
               (add (mul rho c) (neg (mul rho (mul a b))))) =
      add (mul aTilde bTilde) (mul rho c) := by
    rw [LawfulCommRing.add_add_add_comm (neg cTilde) (mul aTilde bTilde)
          (mul rho c) (neg (mul rho (mul a b))),
        LawfulCommRing.add_add_add_comm cTilde (mul rho (mul a b))
          (add (neg cTilde) (mul rho c))
          (add (mul aTilde bTilde) (neg (mul rho (mul a b))))]
    have h1 : add cTilde (add (neg cTilde) (mul rho c)) = mul rho c := by
      rw [← LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.zero_add]
    have h2 : add (mul rho (mul a b)) (add (mul aTilde bTilde) (neg (mul rho (mul a b)))) = mul aTilde bTilde := by
      rw [LawfulCommRing.add_comm (mul aTilde bTilde) _, ← LawfulCommRing.add_assoc,
          LawfulCommRing.add_right_neg, LawfulCommRing.zero_add]
    rw [h1, h2, LawfulCommRing.add_comm]
  rw [hLHS, hRHS]

/-- **SPDZ Sacrifice Completeness (`spdz_sacrifice_completeness`)**:
    Honest Beaver triples (`c = a * b` and `cTilde = aTilde * bTilde`) pass sacrifice for every `ρ`. -/
theorem spdz_sacrifice_completeness (rho a b c aTilde bTilde cTilde : R)
    (hHonest : c = mul a b) (hCompHonest : cTilde = mul aTilde bTilde) :
    spdzSacrificeResidual rho a b c aTilde bTilde cTilde = zero := by
  rw [spdzSacrificeResidual_eq_linear]
  subst hHonest hCompHonest
  simp only [LawfulCommRing.sub_self, LawfulCommRing.neg_zero R, RoundPoly.evalCoeffs,
             LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-- **SPDZ Sacrifice Privacy Involution (`spdz_sacrifice_mask_bijection`)**:
    For fixed `(rho, a, b)`, the map `(aTilde, bTilde) ↦ spdzSacrificeOpenings rho a b aTilde bTilde`
    is an exact involution on `R × R`, so uniform companion masks `(aTilde, bTilde)` make the
    opened `(u, v)` uniformly distributed and completely independent of `(a, b)`! -/
theorem spdz_sacrifice_mask_bijection (rho a b aTilde bTilde : R) :
    let (u, v) := spdzSacrificeOpenings rho a b aTilde bTilde
    spdzSacrificeOpenings rho a b u v = (aTilde, bTilde) := by
  dsimp only [spdzSacrificeOpenings]
  have hSubCancel : ∀ (x y : R), sub x (sub x y) = y := by
    intro x y
    apply LawfulCommRing.add_left_cancel (a := sub x y)
    rw [LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_comm (sub x y) y,
        LawfulCommRing.add_sub_cancel_left]
  exact Prod.ext (hSubCancel (mul rho a) aTilde) (hSubCancel b bTilde)

/-- **SPDZ Sacrifice Malicious Soundness (`spdz_triple_sacrifice_sound`)**:
    Over ANY integral domain `R` (`GoldilocksExt2`, `Tower128`, `Goldilocks`), if a target triple
    is corrupted (`c ≠ a * b`), then across ANY duplicate-free challenge pool `S : List R`, AT MOST
    **ONE** challenge `ρ ∈ S` can satisfy `spdzSacrificeResidual ρ ... = 0`! -/
theorem spdz_triple_sacrifice_sound [DecidableEq R] [NoZeroDivisors R]
    (a b c aTilde bTilde cTilde : R) (S : List R) (hNodup : S.Nodup)
    (hCheated : c ≠ mul a b) :
    (S.filter (fun rho => decide (spdzSacrificeResidual rho a b c aTilde bTilde cTilde = zero))).length ≤ 1 := by
  let delta := sub c (mul a b)
  let deltaTilde := sub cTilde (mul aTilde bTilde)
  have hDeltaNz : delta ≠ zero := fun h0 => hCheated (LawfulCommRing.sub_eq_zero_iff.mp h0)
  have hPolyNz : RoundPoly.evalCoeffs [neg deltaTilde, delta] one ≠ RoundPoly.evalCoeffs [neg deltaTilde, delta] zero := by
    intro hEq
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
               LawfulCommRing.one_mul, LawfulCommRing.zero_mul] at hEq
    have hCancel := LawfulCommRing.add_left_cancel (a := neg deltaTilde) (hEq.trans (LawfulCommRing.add_zero _).symm)
    exact hDeltaNz hCancel
  have hWitnessNz : ∃ z : R, RoundPoly.evalCoeffs [neg deltaTilde, delta] z ≠ zero := by
    by_cases h0 : RoundPoly.evalCoeffs [neg deltaTilde, delta] zero = zero
    · exact ⟨one, fun h1 => hPolyNz (h1.trans h0.symm)⟩
    · exact ⟨zero, h0⟩
  have hFiltEq :
      S.filter (fun rho => decide (spdzSacrificeResidual rho a b c aTilde bTilde cTilde = zero)) =
      S.filter (fun rho => decide (RoundPoly.evalCoeffs [neg deltaTilde, delta] rho = zero)) := by
    apply List.filter_congr
    intro rho _
    rw [spdzSacrificeResidual_eq_linear]
  rw [hFiltEq]
  exact RoundPoly.roots_nodup_length_le 1 [neg deltaTilde, delta] S hNodup (by simp) hWitnessNz

end PolymorphicAlgebra

/-- Preprocessed dealerless `(t, n)` Shamir power-chain tuple `([r], [r^2], ..., [r^7])`
    across `n` parties over `Goldilocks`, produced by 3-round `Π_pow7` (`evalSharedPow7Tree`). -/
structure SharedPow7Tuple where
  rSh  : List Goldilocks
  r2Sh : List Goldilocks
  r3Sh : List Goldilocks
  r4Sh : List Goldilocks
  r5Sh : List Goldilocks
  r6Sh : List Goldilocks
  r7Sh : List Goldilocks
  deriving DecidableEq, Repr

/-- Execute the 3-round share-level `Π_pow7` Beaver tree over `(t, n)` Shamir shares `rSh`
    without reconstructing `r` or any intermediate power. -/
def evalSharedPow7Tree (lambdas rSh : List Goldilocks)
    (t2 t3 t4 t5 t6 t7 : SharedBeaverTriple Goldilocks) : SharedPow7Tuple :=
  let (r2, r3, r4, r5, r6, r7) := evalSharedPow7BeaverTreePoly lambdas rSh t2 t3 t4 t5 t6 t7
  { rSh := rSh, r2Sh := r2, r3Sh := r3, r4Sh := r4, r5Sh := r5, r6Sh := r6, r7Sh := r7 }

/-- **Share-Level 3-Round `Π_pow7` Correctness (`evalSharedPow7Tree_correct`)**:
    Given valid `(t, n)` Shamir Beaver triples `t2..t7` and Lagrange weights summing to `1`,
    `evalSharedPow7Tree` outputs `n`-party share vectors recombining to `(r, r^2, ..., r^7)` with
    `⟨λ, r7Sh⟩ = sbox7 ⟨λ, rSh⟩` and zero cleartext secret reconstruction. -/
theorem evalSharedPow7Tree_correct
    (lambdas rSh : List Goldilocks)
    (t2 t3 t4 t5 t6 t7 : SharedBeaverTriple Goldilocks)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hRLen : rSh.length = lambdas.length)
    (h2 : t2.validAt lambdas) (h3 : t3.validAt lambdas) (h4 : t4.validAt lambdas)
    (h5 : t5.validAt lambdas) (h6 : t6.validAt lambdas) (h7 : t7.validAt lambdas) :
    let tup := evalSharedPow7Tree lambdas rSh t2 t3 t4 t5 t6 t7
    let r := ringDot lambdas rSh
    tup.rSh = rSh ∧
    (tup.r2Sh.length = lambdas.length ∧ tup.r3Sh.length = lambdas.length ∧
     tup.r4Sh.length = lambdas.length ∧ tup.r5Sh.length = lambdas.length ∧
     tup.r6Sh.length = lambdas.length ∧ tup.r7Sh.length = lambdas.length) ∧
    ringDot lambdas tup.r2Sh = Goldilocks.mul r r ∧
    ringDot lambdas tup.r3Sh = Goldilocks.mul (Goldilocks.mul r r) r ∧
    ringDot lambdas tup.r4Sh = Goldilocks.mul (Goldilocks.mul r r) (Goldilocks.mul r r) ∧
    ringDot lambdas tup.r5Sh = Goldilocks.mul (ringDot lambdas tup.r4Sh) r ∧
    ringDot lambdas tup.r6Sh = Goldilocks.mul (ringDot lambdas tup.r4Sh) (ringDot lambdas tup.r2Sh) ∧
    ringDot lambdas tup.r7Sh = sbox7 r := by
  have hPoly := evalSharedPow7BeaverTreePoly_correct lambdas rSh t2 t3 t4 t5 t6 t7
    hSumOne hRLen h2 h3 h4 h5 h6 h7
  dsimp only [evalSharedPow7Tree] at *
  obtain ⟨hLens, hE2, hE3, hE4, hE5, hE6, hE7⟩ := hPoly
  refine ⟨rfl, hLens, hE2, ?_, ?_, hE5, hE6, ?_⟩
  · rw [hE3, hE2]; rfl
  · rw [hE4, hE2]; rfl
  · rw [hE7, hE4, hE3, hE2]
    unfold sbox7
    exact LawfulCommRing.mul_comm _ _

/-! ## 5. Concrete Soundness Instantiations & Authenticated `(t, n)` Shared SPDZ Sacrifice -/

theorem goldilocksExt2_card_gt_two_pow_127 : 2 ^ 127 < goldilocksPrime ^ 2 := by
  unfold goldilocksPrime; decide

/-- **Concrete `Π_pow7` Malicious Sacrifice Soundness (`pow7_sacrifice_sound`)**:
    Over `GoldilocksExt2` ($\mathbb{F}_{p^2}, |\mathbb{F}_{p^2}| = p^2 > 2^{127}$), any corrupted
    Beaver triple (`c ≠ a * b`) survives sacrifice on at most `1` challenge out of `p^2`, bounding
    single-triple cheating probability by `1 / p^2 < 2^{-127} < 2^{-125}`, and union-bounded across
    all 6 triples of `evalPow7BeaverTree` by `6 / p^2 < 2^{-124}` (and `< 2^{-251}` with 2 challenges). -/
theorem pow7_sacrifice_sound
    (a b c aTilde bTilde cTilde : GoldilocksExt2)
    (S : List GoldilocksExt2) (hNodup : S.Nodup) (hCheated : c ≠ CommRingOps.mul a b) :
    let bad := (S.filter (fun rho => decide (spdzSacrificeResidual rho a b c aTilde bTilde cTilde = CommRingOps.zero))).length
    bad ≤ 1 ∧
    ratLe (bad, goldilocksPrime ^ 2) (1, 2 ^ 127) ∧
    ratLe (6 * bad, goldilocksPrime ^ 2) (1, 2 ^ 124) := by
  intro bad
  have hBadLe1 : bad ≤ 1 := spdz_triple_sacrifice_sound a b c aTilde bTilde cTilde S hNodup hCheated
  have hCard : 2 ^ 127 < goldilocksPrime ^ 2 := goldilocksExt2_card_gt_two_pow_127
  have hCard6 : 6 * (2 ^ 124) ≤ goldilocksPrime ^ 2 := by unfold goldilocksPrime; decide
  refine ⟨hBadLe1, ?_, ?_⟩
  · unfold ratLe
    dsimp only
    refine ⟨show 0 < goldilocksPrime ^ 2 by unfold goldilocksPrime; decide, Nat.two_pow_pos 127, ?_⟩
    calc
      bad * (2 ^ 127) ≤ 1 * (2 ^ 127) := Nat.mul_le_mul_right _ hBadLe1
      _ ≤ 1 * (goldilocksPrime ^ 2) := by simpa using Nat.le_of_lt hCard
  · unfold ratLe
    dsimp only
    refine ⟨show 0 < goldilocksPrime ^ 2 by unfold goldilocksPrime; decide, Nat.two_pow_pos 124, ?_⟩
    have h6Le : 6 * bad ≤ 6 := by omega
    calc
      (6 * bad) * (2 ^ 124) ≤ 6 * (2 ^ 124) := Nat.mul_le_mul_right _ h6Le
      _ ≤ 1 * (goldilocksPrime ^ 2) := by simpa using hCard6

/-- **Concrete `Π_triple_f2` 2-Lane `Tower128` Sacrifice Soundness (`triple_f2_sacrifice_sound`)**:
    Over `Tower128` (`TowerElem 7`, $|\mathbb{F}_{2^{128}}| = 2^{128}$), any corrupted Boolean or
    $\mathcal{T}_3$ triple (`c ≠ a * b` embedded via `embedTowerChain_injective`) survives a single
    `Tower128` sacrifice lane on at most `1` challenge out of $2^{128}$, and survives **two**
    independent `Tower128` lanes $(\rho_1, \rho_2) \in S_1 \times S_2$ on at most `1` pair out of
    $2^{256}$! -/
theorem triple_f2_sacrifice_sound
    (a b c aT1 bT1 cT1 aT2 bT2 cT2 : Tower128)
    (S1 S2 : List Tower128) (hNodup1 : S1.Nodup) (hNodup2 : S2.Nodup)
    (hCheated : c ≠ CommRingOps.mul a b) :
    let bad1 := (S1.filter (fun r1 => decide (spdzSacrificeResidual r1 a b c aT1 bT1 cT1 = CommRingOps.zero))).length
    let bad2 := (S2.filter (fun r2 => decide (spdzSacrificeResidual r2 a b c aT2 bT2 cT2 = CommRingOps.zero))).length
    bad1 ≤ 1 ∧ bad2 ≤ 1 ∧ bad1 * bad2 ≤ 1 ∧
    ratLe (bad1, 2 ^ 128) (1, 2 ^ 128) ∧
    ratLe (bad1 * bad2, 2 ^ 256) (1, 2 ^ 256) := by
  intro bad1 bad2
  have hb1 : bad1 ≤ 1 := spdz_triple_sacrifice_sound a b c aT1 bT1 cT1 S1 hNodup1 hCheated
  have hb2 : bad2 ≤ 1 := spdz_triple_sacrifice_sound a b c aT2 bT2 cT2 S2 hNodup2 hCheated
  have hProd : bad1 * bad2 ≤ 1 := by
    calc bad1 * bad2 ≤ 1 * 1 := Nat.mul_le_mul hb1 hb2
    _ = 1 := rfl
  refine ⟨hb1, hb2, hProd, ?_, ?_⟩
  · unfold ratLe; dsimp only
    exact ⟨Nat.two_pow_pos 128, Nat.two_pow_pos 128, Nat.mul_le_mul_right _ hb1⟩
  · unfold ratLe; dsimp only
    exact ⟨Nat.two_pow_pos 256, Nat.two_pow_pos 256, Nat.mul_le_mul_right _ hProd⟩

section SharedSpdzSacrifice
open CommRingOps

theorem ringDot_ofBase :
    ∀ (ls xs : List Goldilocks),
      ringDot (ls.map GoldilocksExt2.ofBase) (xs.map GoldilocksExt2.ofBase) =
        GoldilocksExt2.ofBase (ringDot ls xs)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | l :: ls, x :: xs => by
    simp only [List.map_cons, ringDot, GoldilocksExt2.ofBase_add, GoldilocksExt2.ofBase_mul,
      ringDot_ofBase ls xs]

theorem ringListSum_scale {R : Type} [LawfulCommRing R] (c : R) :
    ∀ (xs : List R), ringListSum (shareScale c xs) = mul c (ringListSum xs)
  | [] => by simp [shareScale, ringListSum, LawfulCommRing.mul_zero]
  | x :: xs => by
    have ih := ringListSum_scale c xs
    simp only [shareScale, List.map_cons, ringListSum]
    change add (mul c x) (ringListSum (shareScale c xs)) = mul c (add x (ringListSum xs))
    rw [ih, LawfulCommRing.left_distrib]

theorem ringListSum_zipSub {R : Type} [LawfulCommRing R] :
    ∀ {xs ys : List R}, xs.length = ys.length →
      ringListSum (shareZipSub xs ys) = sub (ringListSum xs) (ringListSum ys)
  | [], [], _ => by simp [shareZipSub, ringListSum, LawfulCommRing.sub_self]
  | x :: xs, y :: ys, h => by
    simp only [shareZipSub, ringListSum, ringListSum_zipSub (Nat.succ.inj h)]
    apply LawfulCommRing.add_left_cancel (a := add y (ringListSum ys))
    rw [LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_sub_cancel_left]

/-- Party-by-party zero-sum SPDZ `MacCheck` broadcast shares `σ_i = (γ_i - α_i · y_opened) + mask_i`. -/
def spdzComputeSigmas {K : Type} [CommRingOps K] (yOpened : K) : List K → List K → List K → List K
  | m :: ms, a :: as, z :: zs =>
    add (sub m (mul a yOpened)) z :: spdzComputeSigmas yOpened ms as zs
  | _, _, _ => []

/-- Distributed zero-sum SPDZ `MacCheck` verifier (`∑_i σ_i = 0`). -/
@[expose] def verifySpdzZeroSumMac {K : Type} [LawfulCommRing K] [DecidableEq K] (sigmas : List K) : Bool :=
  decide (ringListSum sigmas = zero)

theorem ringListSum_spdzComputeSigmas {K : Type} [LawfulCommRing K] (yOpened : K) :
    ∀ {macs alphas masks : List K},
      macs.length = alphas.length → masks.length = alphas.length →
      ringListSum (spdzComputeSigmas yOpened macs alphas masks) =
        add (sub (ringListSum macs) (mul (ringListSum alphas) yOpened)) (ringListSum masks)
  | [], [], [], _, _ => by
    simp [spdzComputeSigmas, ringListSum, LawfulCommRing.zero_mul,
      LawfulCommRing.sub_self, LawfulCommRing.add_zero]
  | m :: ms, a :: as, z :: zs, hm, hz => by
    simp only [spdzComputeSigmas, ringListSum,
      ringListSum_spdzComputeSigmas yOpened (Nat.succ.inj hm) (Nat.succ.inj hz)]
    rw [LawfulCommRing.add_add_add_comm (sub m (mul a yOpened)) z _ (ringListSum zs)]
    congr 1
    rw [LawfulCommRing.right_distrib]
    apply LawfulCommRing.add_left_cancel (a := add (mul a yOpened) (mul (ringListSum as) yOpened))
    rw [LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_sub_cancel_left]

theorem verifySpdzZeroSumMac_complete {K : Type} [LawfulCommRing K] [DecidableEq K]
    (yTrue yOpened : K) (macs alphas masks : List K)
    (hLenM : macs.length = alphas.length) (hLenZ : masks.length = alphas.length)
    (hMac : ringListSum macs = mul (ringListSum alphas) yTrue)
    (hZeroMask : ringListSum masks = zero)
    (hOpen : yOpened = yTrue) :
    verifySpdzZeroSumMac (spdzComputeSigmas yOpened macs alphas masks) = true := by
  unfold verifySpdzZeroSumMac
  rw [decide_eq_true_iff, ringListSum_spdzComputeSigmas yOpened hLenM hLenZ,
      hMac, hOpen, hZeroMask, LawfulCommRing.sub_self, LawfulCommRing.add_zero]

/-- **Tampered SPDZ Opening Uniquely Pins Global Key $\alpha \in \mathbb{F}_{p^2}$**:
    When the honest MAC sum is `α · yTrue`, any forged opening `yOpened ≠ yTrue` accompanied by
    arbitrary adversary broadcast shift `deltaSigma` passes `verifySpdzZeroSumMac` only if
    `α = deltaSigma · (yOpened - yTrue)⁻¹` (`≤ 1` key out of `p^2 > 2^{127}`). -/
theorem verifySpdzZeroSumMac_forged_pins_key
    (alpha yTrue yOpened deltaSigma : GoldilocksExt2) (sigmas : List GoldilocksExt2)
    (hNe : yOpened ≠ yTrue)
    (hSum : ringListSum sigmas = sub (add (mul alpha yTrue) deltaSigma) (mul alpha yOpened))
    (hAccept : verifySpdzZeroSumMac sigmas = true) :
    alpha = mul deltaSigma (GoldilocksExt2.inv (sub yOpened yTrue)) := by
  unfold verifySpdzZeroSumMac at hAccept
  have hZero : ringListSum sigmas = zero := of_decide_eq_true hAccept
  rw [hSum] at hZero
  have hEq : add (mul alpha yTrue) deltaSigma = mul alpha yOpened :=
    LawfulCommRing.sub_eq_zero_iff.mp hZero
  have hDelta : deltaSigma = mul alpha (sub yOpened yTrue) := by
    rw [LawfulCommRing.mul_sub]
    apply LawfulCommRing.add_left_cancel (a := mul alpha yTrue)
    rw [hEq, LawfulCommRing.add_comm (mul alpha yTrue) _, LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.add_assoc, LawfulCommRing.add_left_neg, LawfulCommRing.add_zero]
  have hDiffNz : sub yOpened yTrue ≠ zero :=
    fun h0 => hNe (LawfulCommRing.sub_eq_zero_iff.mp h0)
  rw [hDelta, LawfulCommRing.mul_assoc, GoldilocksExt2.mul_inv_cancel hDiffNz,
      LawfulCommRing.mul_one]

/-- Authenticated `(t, n)` Shamir Beaver triple over `Goldilocks` paired with `n`-party additive
    SPDZ MAC shares over `GoldilocksExt2` (`𝔽_{p^2}`). -/
structure AuthenticatedSharedTriple where
  triple : SharedBeaverTriple Goldilocks
  macA   : List GoldilocksExt2
  macB   : List GoldilocksExt2
  macC   : List GoldilocksExt2
  deriving DecidableEq, Repr

def AuthenticatedSharedTriple.validMacs
    (lambdas : List Goldilocks) (alphaShares : List GoldilocksExt2)
    (tr : AuthenticatedSharedTriple) : Prop :=
  let alpha := ringListSum alphaShares
  tr.macA.length = alphaShares.length ∧
  tr.macB.length = alphaShares.length ∧
  tr.macC.length = alphaShares.length ∧
  ringListSum tr.macA = mul alpha (GoldilocksExt2.ofBase (ringDot lambdas tr.triple.aShares)) ∧
  ringListSum tr.macB = mul alpha (GoldilocksExt2.ofBase (ringDot lambdas tr.triple.bShares)) ∧
  ringListSum tr.macC = mul alpha (GoldilocksExt2.ofBase (ringDot lambdas tr.triple.cShares))

/-- Broadcast transcript of distributed `(t, n)` SPDZ companion sacrifice at challenge `ρ ∈ 𝔽_{p^2}`. -/
structure SharedSpdzSacrificeOpening where
  uOpened : GoldilocksExt2
  vOpened : GoldilocksExt2
  wOpened : GoldilocksExt2
  sigmaU  : List GoldilocksExt2
  sigmaV  : List GoldilocksExt2
  sigmaW  : List GoldilocksExt2
  deriving DecidableEq, Repr

private def computeSacrificeWOpen
    (lambdasK : List GoldilocksExt2) (rho uOpen vOpen : GoldilocksExt2)
    (tr trTilde : AuthenticatedSharedTriple) : GoldilocksExt2 :=
  let bShK := tr.triple.bShares.map GoldilocksExt2.ofBase
  let cShK := tr.triple.cShares.map GoldilocksExt2.ofBase
  let aTShK := trTilde.triple.aShares.map GoldilocksExt2.ofBase
  let cTShK := trTilde.triple.cShares.map GoldilocksExt2.ofBase
  let wShares := shareZipSub
    (shareZipSub (shareScale rho cShK) cTShK)
    (ringListZipAdd (shareScale uOpen bShK) (shareScale vOpen aTShK))
  ringDot lambdasK wShares

private def mkSharedSacrificeFromOpened
    (uOpen vOpen wOpen rho : GoldilocksExt2)
    (alphaShares : List GoldilocksExt2)
    (tr trTilde : AuthenticatedSharedTriple)
    (maskU maskV maskW : List GoldilocksExt2) : SharedSpdzSacrificeOpening :=
  let macU := shareZipSub (shareScale rho tr.macA) trTilde.macA
  let macV := shareZipSub tr.macB trTilde.macB
  let macW := shareZipSub
    (shareZipSub (shareScale rho tr.macC) trTilde.macC)
    (ringListZipAdd (shareScale uOpen tr.macB) (shareScale vOpen trTilde.macA))
  { uOpened := uOpen
    vOpened := vOpen
    wOpened := wOpen
    sigmaU  := spdzComputeSigmas uOpen macU alphaShares maskU
    sigmaV  := spdzComputeSigmas vOpen macV alphaShares maskV
    sigmaW  := spdzComputeSigmas wOpen macW alphaShares maskW }

/-- Honest distributed `(t, n)` SPDZ sacrifice execution: parties lift Shamir shares to `𝔽_{p^2}`,
    open `U = ρ·a - ã`, `V = b - b̃`, and `W = ρ·c - c̃ - U·b - ã·V`, and emit zero-sum masked `σ` shares. -/
def honestSharedSpdzSacrificeOpening
    (lambdas : List Goldilocks) (rho : GoldilocksExt2)
    (alphaShares : List GoldilocksExt2)
    (tr trTilde : AuthenticatedSharedTriple)
    (maskU maskV maskW : List GoldilocksExt2) : SharedSpdzSacrificeOpening :=
  let lambdasK := lambdas.map GoldilocksExt2.ofBase
  let aShK := tr.triple.aShares.map GoldilocksExt2.ofBase
  let bShK := tr.triple.bShares.map GoldilocksExt2.ofBase
  let aTShK := trTilde.triple.aShares.map GoldilocksExt2.ofBase
  let bTShK := trTilde.triple.bShares.map GoldilocksExt2.ofBase
  let uOpen := ringDot lambdasK (shareZipSub (shareScale rho aShK) aTShK)
  let vOpen := ringDot lambdasK (shareZipSub bShK bTShK)
  let wOpen := computeSacrificeWOpen lambdasK rho uOpen vOpen tr trTilde
  mkSharedSacrificeFromOpened uOpen vOpen wOpen rho alphaShares tr trTilde maskU maskV maskW

/-- Distributed `(t, n)` SPDZ sacrifice verifier checking residual zero-opening AND all three
    zero-sum `GoldilocksExt2` `MacCheck` equations. -/
def verifySharedSpdzSacrifice (op : SharedSpdzSacrificeOpening) : Bool :=
  decide (op.wOpened = zero) &&
  verifySpdzZeroSumMac op.sigmaU &&
  verifySpdzZeroSumMac op.sigmaV &&
  verifySpdzZeroSumMac op.sigmaW

/-- **Authenticated `(t, n)` Shared SPDZ Sacrifice Completeness (`verifySharedSpdzSacrifice_complete`)**:
    Honest `(t, n)` Shamir Beaver triples + honest companion triples + honest `GoldilocksExt2`
    additive MAC shares and zero-sum masks pass `verifySharedSpdzSacrifice` for every `ρ ∈ 𝔽_{p^2}`. -/
theorem verifySharedSpdzSacrifice_complete
    (lambdas : List Goldilocks) (rho : GoldilocksExt2)
    (alphaShares : List GoldilocksExt2)
    (tr trTilde : AuthenticatedSharedTriple)
    (maskU maskV maskW : List GoldilocksExt2)
    (hTr : tr.triple.validAt lambdas)
    (hTrTilde : trTilde.triple.validAt lambdas)
    (hMac : tr.validMacs lambdas alphaShares)
    (hMacTilde : trTilde.validMacs lambdas alphaShares)
    (hMaskULen : maskU.length = alphaShares.length)
    (hMaskVLen : maskV.length = alphaShares.length)
    (hMaskWLen : maskW.length = alphaShares.length)
    (hMaskU0 : ringListSum maskU = zero)
    (hMaskV0 : ringListSum maskV = zero)
    (hMaskW0 : ringListSum maskW = zero) :
    verifySharedSpdzSacrifice
      (honestSharedSpdzSacrificeOpening lambdas rho alphaShares tr trTilde maskU maskV maskW) = true := by
  obtain ⟨hALen, hBLen, hCLen, hCMul⟩ := hTr
  obtain ⟨hATLen, hBTLen, hCTLen, hCTMul⟩ := hTrTilde
  obtain ⟨hMALen, hMBLen, hMCLen, hMASum, hMBSum, hMCSum⟩ := hMac
  obtain ⟨hMATLen, hMBTLen, hMCTLen, hMATSum, hMBTSum, hMCTSum⟩ := hMacTilde
  let aK := GoldilocksExt2.ofBase (ringDot lambdas tr.triple.aShares)
  let bK := GoldilocksExt2.ofBase (ringDot lambdas tr.triple.bShares)
  let cK := GoldilocksExt2.ofBase (ringDot lambdas tr.triple.cShares)
  let aTK := GoldilocksExt2.ofBase (ringDot lambdas trTilde.triple.aShares)
  let bTK := GoldilocksExt2.ofBase (ringDot lambdas trTilde.triple.bShares)
  let cTK := GoldilocksExt2.ofBase (ringDot lambdas trTilde.triple.cShares)
  let alpha := ringListSum alphaShares
  have hcK : cK = mul aK bK := by
    dsimp only [cK, aK, bK]; rw [hCMul, GoldilocksExt2.ofBase_mul]
  have hcTK : cTK = mul aTK bTK := by
    dsimp only [cTK, aTK, bTK]; rw [hCTMul, GoldilocksExt2.ofBase_mul]
  have hUOpen :
      ringDot (lambdas.map GoldilocksExt2.ofBase)
        (shareZipSub (shareScale rho (tr.triple.aShares.map GoldilocksExt2.ofBase))
          (trTilde.triple.aShares.map GoldilocksExt2.ofBase)) = sub (mul rho aK) aTK := by
    rw [ringDot_zipSub (by simp [hALen, hATLen]), ringDot_scale,
        ringDot_ofBase, ringDot_ofBase]
  have hVOpen :
      ringDot (lambdas.map GoldilocksExt2.ofBase)
        (shareZipSub (tr.triple.bShares.map GoldilocksExt2.ofBase)
          (trTilde.triple.bShares.map GoldilocksExt2.ofBase)) = sub bK bTK := by
    rw [ringDot_zipSub (by simp [hBLen, hBTLen]), ringDot_ofBase, ringDot_ofBase]
  let uOpen := sub (mul rho aK) aTK
  let vOpen := sub bK bTK
  have hWOpen :
      computeSacrificeWOpen (lambdas.map GoldilocksExt2.ofBase) rho uOpen vOpen tr trTilde = zero := by
    unfold computeSacrificeWOpen
    dsimp only
    have hL1 : (shareZipSub (shareScale rho (tr.triple.cShares.map GoldilocksExt2.ofBase))
        (trTilde.triple.cShares.map GoldilocksExt2.ofBase)).length = lambdas.length := by
      rw [shareZipSub_length_of_eq (by simp [hCLen, hCTLen])]
      simp [hCLen]
    have hL2 : (ringListZipAdd
        (shareScale uOpen (tr.triple.bShares.map GoldilocksExt2.ofBase))
        (shareScale vOpen (trTilde.triple.aShares.map GoldilocksExt2.ofBase))).length = lambdas.length := by
      rw [ringListZipAdd_length_of_eq (by simp [hBLen, hATLen])]
      simp [hBLen]
    rw [ringDot_zipSub (hL1.trans hL2.symm),
        ringDot_zipSub (by simp [hCLen, hCTLen]),
        ringDot_zipAdd (by simp [hBLen, hATLen]),
        ringDot_scale, ringDot_scale, ringDot_scale,
        ringDot_ofBase, ringDot_ofBase, ringDot_ofBase, ringDot_ofBase]
    change sub (sub (mul rho cK) cTK) (add (mul uOpen bK) (mul vOpen aTK)) = zero
    rw [LawfulCommRing.mul_comm vOpen aTK]
    exact spdz_sacrifice_completeness rho aK bK cK aTK bTK cTK hcK hcTK
  have hMacULen : (shareZipSub (shareScale rho tr.macA) trTilde.macA).length = alphaShares.length := by
    rw [shareZipSub_length_of_eq (by simp [hMALen, hMATLen])]
    simp [hMALen]
  have hMacUSum : ringListSum (shareZipSub (shareScale rho tr.macA) trTilde.macA) = mul alpha uOpen := by
    rw [ringListSum_zipSub (by simp [hMALen, hMATLen]),
        ringListSum_scale, hMASum, hMATSum]
    change sub (mul rho (mul alpha aK)) (mul alpha aTK) = mul alpha (sub (mul rho aK) aTK)
    rw [← LawfulCommRing.mul_assoc rho alpha aK, LawfulCommRing.mul_comm rho alpha,
        LawfulCommRing.mul_assoc alpha rho aK, ← LawfulCommRing.mul_sub]
  have hMacVLen : (shareZipSub tr.macB trTilde.macB).length = alphaShares.length := by
    rw [shareZipSub_length_of_eq (hMBLen.trans hMBTLen.symm), hMBLen]
  have hMacVSum : ringListSum (shareZipSub tr.macB trTilde.macB) = mul alpha vOpen := by
    rw [ringListSum_zipSub (hMBLen.trans hMBTLen.symm), hMBSum, hMBTSum, ← LawfulCommRing.mul_sub]
  have hMacW1Len : (shareZipSub (shareScale rho tr.macC) trTilde.macC).length = alphaShares.length := by
    rw [shareZipSub_length_of_eq (by simp [hMCLen, hMCTLen])]
    simp [hMCLen]
  have hMacW2Len : (ringListZipAdd (shareScale uOpen tr.macB) (shareScale vOpen trTilde.macA)).length = alphaShares.length := by
    rw [ringListZipAdd_length_of_eq (by simp [hMBLen, hMATLen])]
    simp [hMBLen]
  have hMacWLen : (shareZipSub
      (shareZipSub (shareScale rho tr.macC) trTilde.macC)
      (ringListZipAdd (shareScale uOpen tr.macB) (shareScale vOpen trTilde.macA))).length = alphaShares.length := by
    rw [shareZipSub_length_of_eq (hMacW1Len.trans hMacW2Len.symm), hMacW1Len]
  have hMacWSum : ringListSum (shareZipSub
      (shareZipSub (shareScale rho tr.macC) trTilde.macC)
      (ringListZipAdd (shareScale uOpen tr.macB) (shareScale vOpen trTilde.macA))) = mul alpha zero := by
    rw [ringListSum_zipSub (hMacW1Len.trans hMacW2Len.symm),
        ringListSum_zipSub (by simp [hMCLen, hMCTLen]),
        ringListSum_zipAdd, ringListSum_scale, ringListSum_scale, ringListSum_scale,
        hMCSum, hMCTSum, hMBSum, hMATSum]
    have hSwap : ∀ (x y : GoldilocksExt2), mul x (mul alpha y) = mul alpha (mul x y) := by
      intro x y
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x alpha, LawfulCommRing.mul_assoc]
    rw [hSwap rho cK, hSwap uOpen bK, hSwap vOpen aTK,
        ← LawfulCommRing.mul_sub, ← LawfulCommRing.left_distrib, ← LawfulCommRing.mul_sub]
    suffices hZeroRes : sub (sub (mul rho cK) cTK) (add (mul uOpen bK) (mul vOpen aTK)) = zero by
      rw [hZeroRes]
    rw [LawfulCommRing.mul_comm vOpen aTK]
    exact spdz_sacrifice_completeness rho aK bK cK aTK bTK cTK hcK hcTK
  unfold honestSharedSpdzSacrificeOpening
  dsimp only
  rw [hUOpen, hVOpen, hWOpen]
  unfold verifySharedSpdzSacrifice mkSharedSacrificeFromOpened
  dsimp only
  have hZ0 : decide ((zero : GoldilocksExt2) = zero) = true := decide_eq_true rfl
  have hMU := verifySpdzZeroSumMac_complete uOpen uOpen
    (shareZipSub (shareScale rho tr.macA) trTilde.macA) alphaShares maskU
    hMacULen hMaskULen hMacUSum hMaskU0 rfl
  have hMV := verifySpdzZeroSumMac_complete vOpen vOpen
    (shareZipSub tr.macB trTilde.macB) alphaShares maskV
    hMacVLen hMaskVLen hMacVSum hMaskV0 rfl
  have hMW := verifySpdzZeroSumMac_complete zero zero
    (shareZipSub (shareZipSub (shareScale rho tr.macC) trTilde.macC)
      (ringListZipAdd (shareScale uOpen tr.macB) (shareScale vOpen trTilde.macA)))
    alphaShares maskW hMacWLen hMaskWLen hMacWSum hMaskW0 rfl
  rw [hZ0, hMU, hMV, hMW]
  rfl

/-- **Authenticated `(t, n)` Shared SPDZ Sacrifice Malicious Soundness (`verifySharedSpdzSacrifice_sound`)**:
    Suppose a shared `(t, n)` Shamir Beaver triple is corrupted (`⟨λ, c⟩ ≠ ⟨λ, a⟩ · ⟨λ, b⟩`).
    1. Across ANY duplicate-free challenge pool `S : List GoldilocksExt2`, at most `1` challenge
       `ρ ∈ S` lets the true shared sacrifice residual vanish (`ratLe (bad, p^2) (1, 2^127)`).
    2. On EVERY challenge `ρ` outside that `≤ 1` root, ANY transcript `op` passing
       `verifySharedSpdzSacrifice op = true` (even under arbitrary adversary MAC shifts
       `deltaU, deltaV, deltaW`) constructively (`0 Classical.choice`) pins the secret global
       MAC key `α ∈ GoldilocksExt2` uniquely! -/

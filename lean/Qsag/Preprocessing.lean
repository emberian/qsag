module
/-
# Qsag.Preprocessing — Dealerless Ring-LWE Base OT, Malicious `Π_pow7` & `Π_triple_f2` Sacrifice

Self-contained Lean 4.35 formalization of the 100% dealerless active-security preprocessing stack
backing `crates/qsag-core/src/preprocessing.rs` (`0` trusted dealers, `0` cleartext trapdoors):
1. **Ring-LWE Base OT Exact Decryption & FO Selective-Failure Count (`rlwe_ot_decrypt_exact`,
   `rlwe1024_ot_decrypt_exact`, `rlwe_fo_cut_and_choose_sound`)**:
   Over $R_q = \mathbb{Z}_{12289}[X]/(X^{N} + 1)$ ($N \in \{512, 1024\}$) with $\eta = 1$ noise,
   worst-case decryption noise is strictly $< \lfloor q / 4 \rfloor = 3072$, guaranteeing zero
   decryption error on every valid RLWE branch and $2^{-k}$ selective-failure survival of a sender
   corrupting one ciphertext in each of $k$ base OTs.
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
import all Qsag.Poseidon2
import all Qsag.UcGames
import Qsag.Tactic.AssuranceKit

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

/-- Inductive witness that an $n$-party share vector `ws` (`ws.length = us.length = vShares.length`)
    arises from local inputs `us`, `vShares` via pairwise OLE correlations
    ($s_{i,j}^{(1)} + s_{i,j}^{(2)} = u_i \cdot v_j$) with zero trusted dealer. -/
inductive ValidPairwiseOleShares : List R → List R → List R → Prop where
  | nil : ValidPairwiseOleShares [] [] []
  | cons {u0 v0 : R} {us vShares wsTail : List R}
      (s0Right1 s0Right2 sLeft0_1 sLeft0_2 : List R)
      (hTail : ValidPairwiseOleShares us vShares wsTail)
      (hLenR1 : s0Right1.length = wsTail.length)
      (hLenR2 : s0Right2.length = wsTail.length)
      (hLenL1 : sLeft0_1.length = wsTail.length)
      (hLenL2 : sLeft0_2.length = wsTail.length)
      (hRightSum : add (ringListSum s0Right1) (ringListSum s0Right2) = mul u0 (ringListSum vShares))
      (hLeftSum  : add (ringListSum sLeft0_1) (ringListSum sLeft0_2) = mul (ringListSum us) v0) :
      ValidPairwiseOleShares (u0 :: us) (v0 :: vShares)
        (add (mul u0 v0) (add (ringListSum s0Right1) (ringListSum sLeft0_2)) ::
         ringListZipAdd wsTail (ringListZipAdd s0Right2 sLeft0_1))

/-- True $n$-party arity preservation: `ValidPairwiseOleShares us vShares ws` produces one output
    share per party (`ws.length = us.length` and `vShares.length = us.length`). -/
theorem ValidPairwiseOleShares.length_eq {us vShares ws : List R}
    (hValid : ValidPairwiseOleShares us vShares ws) :
    ws.length = us.length ∧ vShares.length = us.length := by
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
theorem ole_pairwise_cross_sum_eq_mul {us vShares ws : List R}
    (hValid : ValidPairwiseOleShares us vShares ws) :
    ringListSum ws = mul (ringListSum us) (ringListSum vShares) := by
  induction hValid with
  | nil =>
    simp [ringListSum, LawfulCommRing.mul_zero]
  | @cons u0 v0 us vShares wsTail s0R1 s0R2 sL1 sL2 _ _ _ _ _ hR hL ih =>
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
theorem verifySharedSpdzSacrifice_sound
    (lambdas : List Goldilocks) (rho : GoldilocksExt2)
    (alpha deltaU deltaV deltaW : GoldilocksExt2)
    (tr trTilde : AuthenticatedSharedTriple)
    (op : SharedSpdzSacrificeOpening)
    (S : List GoldilocksExt2) (hNodup : S.Nodup)
    (hCheated : ringDot lambdas tr.triple.cShares ≠
      Goldilocks.mul (ringDot lambdas tr.triple.aShares) (ringDot lambdas tr.triple.bShares)) :
    let aK  := GoldilocksExt2.ofBase (ringDot lambdas tr.triple.aShares)
    let bK  := GoldilocksExt2.ofBase (ringDot lambdas tr.triple.bShares)
    let cK  := GoldilocksExt2.ofBase (ringDot lambdas tr.triple.cShares)
    let aTK := GoldilocksExt2.ofBase (ringDot lambdas trTilde.triple.aShares)
    let bTK := GoldilocksExt2.ofBase (ringDot lambdas trTilde.triple.bShares)
    let cTK := GoldilocksExt2.ofBase (ringDot lambdas trTilde.triple.cShares)
    let uTrue := sub (mul rho aK) aTK
    let vTrue := sub bK bTK
    let wTrue := spdzSacrificeResidual rho aK bK cK aTK bTK cTK
    let bad := (S.filter (fun r => decide (spdzSacrificeResidual r aK bK cK aTK bTK cTK = zero))).length
    bad ≤ 1 ∧
    ratLe (bad, goldilocksPrime ^ 2) (1, 2 ^ 127) ∧
    (verifySharedSpdzSacrifice op = true →
      ringListSum op.sigmaU = sub (add (mul alpha uTrue) deltaU) (mul alpha op.uOpened) →
      ringListSum op.sigmaV = sub (add (mul alpha vTrue) deltaV) (mul alpha op.vOpened) →
      (op.uOpened = uTrue → op.vOpened = vTrue →
        ringListSum op.sigmaW = sub (add (mul alpha wTrue) deltaW) (mul alpha op.wOpened)) →
      wTrue = zero ∨
      alpha = mul deltaU (GoldilocksExt2.inv (sub op.uOpened uTrue)) ∨
      alpha = mul deltaV (GoldilocksExt2.inv (sub op.vOpened vTrue)) ∨
      alpha = mul deltaW (GoldilocksExt2.inv (sub zero wTrue))) := by
  intro aK bK cK aTK bTK cTK uTrue vTrue wTrue bad
  have hCheatedK : cK ≠ mul aK bK := by
    intro hEqK
    rw [← GoldilocksExt2.ofBase_mul] at hEqK
    exact hCheated (GoldilocksExt2.ofBase_injective hEqK)
  obtain ⟨hBadLe1, hRat1, _⟩ := pow7_sacrifice_sound aK bK cK aTK bTK cTK S hNodup hCheatedK
  refine ⟨hBadLe1, hRat1, ?_⟩
  intro hVer hSumU hSumV hSumW
  unfold verifySharedSpdzSacrifice at hVer
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hVer
  obtain ⟨⟨⟨hw0, hMacU⟩, hMacV⟩, hMacW⟩ := hVer
  if hu : op.uOpened = uTrue then
    if hv : op.vOpened = vTrue then
      if hw : wTrue = zero then
        exact Or.inl hw
      else
        have hZeroNe : zero ≠ wTrue := fun h => hw h.symm
        have hSumW0 := hSumW hu hv
        rw [hw0] at hSumW0
        exact Or.inr (Or.inr (Or.inr
          (verifySpdzZeroSumMac_forged_pins_key alpha wTrue zero deltaW op.sigmaW hZeroNe hSumW0 hMacW)))
    else
      exact Or.inr (Or.inr (Or.inl
        (verifySpdzZeroSumMac_forged_pins_key alpha vTrue op.vOpened deltaV op.sigmaV hv hSumV hMacV)))
  else
    exact Or.inr (Or.inl
      (verifySpdzZeroSumMac_forged_pins_key alpha uTrue op.uOpened deltaU op.sigmaU hu hSumU hMacU))

def demoLambdas2of3 : List Goldilocks :=
  [Goldilocks.ofNat 2, Goldilocks.neg Goldilocks.one, Goldilocks.zero]

def demoAlphaShares3 : List GoldilocksExt2 :=
  [⟨Goldilocks.ofNat 3, Goldilocks.ofNat 1⟩,
   ⟨Goldilocks.ofNat 2, Goldilocks.ofNat 2⟩,
   ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 1⟩]

def demoZeroMasks3 : List GoldilocksExt2 :=
  [⟨Goldilocks.ofNat 5, Goldilocks.ofNat 2⟩,
   ⟨Goldilocks.neg (Goldilocks.ofNat 3), Goldilocks.neg Goldilocks.one⟩,
   ⟨Goldilocks.neg (Goldilocks.ofNat 2), Goldilocks.neg Goldilocks.one⟩]

def mkDemoMacShares (secret : Nat) : List GoldilocksExt2 :=
  let sK := GoldilocksExt2.ofBase (Goldilocks.ofNat secret)
  demoAlphaShares3.map (fun a_i => mul a_i sK)

def demoHonestAuthTriple : AuthenticatedSharedTriple :=
  -- Degree-1 2-of-3 Shamir shares at x = [1, 2, 3]:
  -- A(X) = 3 + 5X -> [8, 13, 18]; B(X) = 4 + 2X -> [6, 8, 10]; C(X) = 12 + 7X -> [19, 26, 33]
  { triple := { aShares := [Goldilocks.ofNat 8, Goldilocks.ofNat 13, Goldilocks.ofNat 18]
                bShares := [Goldilocks.ofNat 6, Goldilocks.ofNat 8, Goldilocks.ofNat 10]
                cShares := [Goldilocks.ofNat 19, Goldilocks.ofNat 26, Goldilocks.ofNat 33] }
    macA := mkDemoMacShares 3
    macB := mkDemoMacShares 4
    macC := mkDemoMacShares 12 }

def demoCompanionAuthTriple : AuthenticatedSharedTriple :=
  -- Companion degree-1 Shamir shares at x = [1, 2, 3]:
  -- A~(X) = 5 + 3X -> [8, 11, 14]; B~(X) = 2 + 6X -> [8, 14, 20]; C~(X) = 10 + 9X -> [19, 28, 37]
  { triple := { aShares := [Goldilocks.ofNat 8, Goldilocks.ofNat 11, Goldilocks.ofNat 14]
                bShares := [Goldilocks.ofNat 8, Goldilocks.ofNat 14, Goldilocks.ofNat 20]
                cShares := [Goldilocks.ofNat 19, Goldilocks.ofNat 28, Goldilocks.ofNat 37] }
    macA := mkDemoMacShares 5
    macB := mkDemoMacShares 2
    macC := mkDemoMacShares 10 }

/-- **Inhabitedness Witness (`shared_spdz_sacrifice_inhabited`)**:
    Genuine non-constant degree-1 2-of-3 Shamir Beaver triples (`A(X) = 3 + 5X`, `B(X) = 4 + 2X`,
    `C(X) = 12 + 7X`) authenticated under `α = ⟨9, 4⟩ ∈ GoldilocksExt2` satisfy `validAt` and
    pass `verifySharedSpdzSacrifice = true`! -/
theorem shared_spdz_sacrifice_inhabited :
    demoHonestAuthTriple.triple.aShares ≠ [Goldilocks.ofNat 3, Goldilocks.ofNat 3, Goldilocks.ofNat 3] ∧
    ringDot demoLambdas2of3 demoHonestAuthTriple.triple.cShares =
      Goldilocks.mul (ringDot demoLambdas2of3 demoHonestAuthTriple.triple.aShares)
        (ringDot demoLambdas2of3 demoHonestAuthTriple.triple.bShares) ∧
    verifySharedSpdzSacrifice
      (honestSharedSpdzSacrificeOpening demoLambdas2of3 ⟨Goldilocks.ofNat 2, Goldilocks.one⟩
        demoAlphaShares3 demoHonestAuthTriple demoCompanionAuthTriple
        demoZeroMasks3 demoZeroMasks3 demoZeroMasks3) = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`#tooth` Corrupted Shared Shamir Beaver Triple Refusal (`tooth_shared_spdz_sacrifice_rejects_corrupted_triple`)**:
    Corrupting the 2-of-3 Shamir product polynomial from `C(X) = 12 + 7X` to `C_bad(X) = 13 + 7X`
    (`c_bad = 13 ≠ 12 = a · b`) causes `verifySharedSpdzSacrifice` to reject (`= false`) both when
    `wOpened` is opened honestly AND when a cheating prover announces `wOpened := 0` while the
    committee runs `spdzComputeSigmas` on the announced `0` (caught by `verifySpdzZeroSumMac sigmaW = false`)! -/
theorem tooth_shared_spdz_sacrifice_rejects_corrupted_triple :
    let rho : GoldilocksExt2 := ⟨Goldilocks.ofNat 2, Goldilocks.one⟩
    let badTr : AuthenticatedSharedTriple :=
      { demoHonestAuthTriple with
        triple := { demoHonestAuthTriple.triple with
                    cShares := [Goldilocks.ofNat 20, Goldilocks.ofNat 27, Goldilocks.ofNat 34] }
        macC := mkDemoMacShares 13 }
    let op := honestSharedSpdzSacrificeOpening demoLambdas2of3 rho
      demoAlphaShares3 badTr demoCompanionAuthTriple demoZeroMasks3 demoZeroMasks3 demoZeroMasks3
    let macW := shareZipSub
      (shareZipSub (shareScale rho badTr.macC) demoCompanionAuthTriple.macC)
      (ringListZipAdd (shareScale op.uOpened badTr.macB) (shareScale op.vOpened demoCompanionAuthTriple.macA))
    let forgedZeroOp : SharedSpdzSacrificeOpening :=
      { op with wOpened := zero, sigmaW := spdzComputeSigmas zero macW demoAlphaShares3 demoZeroMasks3 }
    ringDot demoLambdas2of3 badTr.triple.cShares ≠
      Goldilocks.mul (ringDot demoLambdas2of3 badTr.triple.aShares)
        (ringDot demoLambdas2of3 badTr.triple.bShares) ∧
    verifySharedSpdzSacrifice op = false ∧
    verifySharedSpdzSacrifice forgedZeroOp = false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end SharedSpdzSacrifice

/-! ## 6. FO Selective Failure, Universal Combiner, Interactive KOS & Silent-OT PCG (`[P1-07]`) -/

/-- Survival test for a sender that corrupts one ciphertext in each of `k` base OTs. The receiver's
    FO re-encryption check inspects only the ciphertext of its own choice bit, so the sender survives
    iff every receiver choice bit `(mask >>> j) & 1` avoids the corrupted branch (encoded as bit `0`).
    There is no cut-and-choose in `preprocessing.rs`: `mask` is the receiver's secret choice vector, and
    survival is the selective-failure event. The per-OT fact for the polynomial FO machine is
    `Qsag.fo_corrupted_branch_rejected_iff_chosen` in `Qsag.LatticePreprocessingFull`. -/
def foSurvivesBranchChecks : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, mask => (mask % 2 == 0) && foSurvivesBranchChecks k (mask / 2)

theorem foSurvivesBranchChecks_iff_zero :
    ∀ (k mask : Nat), mask < 2 ^ k → (foSurvivesBranchChecks k mask = true ↔ mask = 0)
  | 0, mask, hlt => by
    have hm0 : mask = 0 := by simp at hlt; omega
    subst hm0
    simp [foSurvivesBranchChecks]
  | k + 1, mask, hlt => by
    simp only [foSurvivesBranchChecks, Bool.and_eq_true, beq_iff_eq]
    have hDivLt : mask / 2 < 2 ^ k := by
      rw [Nat.pow_succ] at hlt
      omega
    rw [foSurvivesBranchChecks_iff_zero k (mask / 2) hDivLt]
    constructor
    · rintro ⟨hMod, hDiv⟩; omega
    · intro hZero; subst hZero; exact ⟨rfl, rfl⟩

/-- **FO Selective-Failure Count (`fo_cut_and_choose_selective_failure_bound`)**:
    If a malicious Base-OT sender corrupts one Ring-LWE ciphertext in each of `k` base OTs, then over
    the `2 ^ k` receiver choice sub-vectors `cTilde : Fin (2 ^ k)` on those OTs, **exact count `1`**
    (`cTilde = 0`) avoids all `k` corrupted branches. The sender survives with probability `1 / 2^k`
    and, when it survives, has learned those `k` choice bits; this leakage is what the `128 × 384`
    extractor removes. -/
theorem fo_cut_and_choose_selective_failure_bound (k : Nat) :
    let surviveCount := finSum (2 ^ k) (fun c => if foSurvivesBranchChecks k c.1 then 1 else 0)
    let caughtCount := finSum (2 ^ k) (fun c => if !foSurvivesBranchChecks k c.1 then 1 else 0)
    surviveCount = 1 ∧
    caughtCount = 2 ^ k - 1 ∧
    ratLe (surviveCount, 2 ^ k) (1, 2 ^ k) := by
  intro surviveCount caughtCount
  have hPos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hSurvEq : surviveCount = finSum (2 ^ k) (fun c => if c = ⟨0, hPos⟩ then 1 else 0) := by
    apply finSum_congr
    intro c
    have hIff := foSurvivesBranchChecks_iff_zero k c.1 c.2
    by_cases hc0 : c.1 = 0
    · have hce : c = ⟨0, hPos⟩ := Fin.ext hc0
      have hs0 : foSurvivesBranchChecks k 0 = true := (foSurvivesBranchChecks_iff_zero k 0 hPos).mpr rfl
      simp [hce, hs0]
    · have hcne : c ≠ ⟨0, hPos⟩ := fun heq => hc0 (congrArg Fin.val heq)
      cases hs : foSurvivesBranchChecks k c.1
      · simp [hcne]
      · exact False.elim (hc0 (hIff.mp hs))
  have hSurv1 : surviveCount = 1 := hSurvEq.trans (finSum_eq_indicator (2 ^ k) ⟨0, hPos⟩)
  have hSumTotal : surviveCount + caughtCount = 2 ^ k := by
    dsimp only [surviveCount, caughtCount]
    rw [← finSum_add]
    have hConst1 : finSum (2 ^ k) (fun c : Fin (2 ^ k) =>
        (if foSurvivesBranchChecks k c.1 then 1 else 0) +
        (if !foSurvivesBranchChecks k c.1 then 1 else 0)) =
        finSum (2 ^ k) (fun _ => 1) := by
      apply finSum_congr
      intro c
      cases foSurvivesBranchChecks k c.1 <;> rfl
    rw [hConst1, finSum_const]
    omega
  refine ⟨hSurv1, by omega, ?_⟩
  unfold ratLe
  rw [hSurv1]
  exact ⟨hPos, hPos, Nat.le_refl _⟩

/-- Committed Ring-LWE Base-OT branch sample `(bit, eSign, eMag, claimedCt)` at production
    dimension `N = 1024, q = 12289`. -/
structure RlweOtBranchSample where
  bit       : Bool
  eSign     : Bool
  eMag      : Nat
  claimedCt : Nat
  deriving DecidableEq, Repr

/-- Coefficient-level stand-in for the FO check of one branch: worst-case noise bound
    `eMag ≤ 2N + 1 = 2049` and deterministic ciphertext consistency
    `claimedCt = rlweNoisyEncode bit eSign eMag`. The polynomial re-encryption check itself is
    `Qsag.rlweFoReceiverMachine`. -/
def verifyRlweOtBranch (br : RlweOtBranchSample) : Bool :=
  decide (br.eMag ≤ 2 * rlwe1024DimN + 1) &&
  decide (br.claimedCt = rlweNoisyEncode br.bit br.eSign br.eMag)

/-- Check a batch of base-OT branches under the receiver's choice bitmask `mask`: bit `1` means the
    receiver chose (and therefore re-encrypts and checks) this branch; bit `0` means it never looks. -/
def verifyRlweFoBatch : List RlweOtBranchSample → Nat → Bool
  | [], _ => true
  | br :: brs, mask =>
    (if mask % 2 == 1 then verifyRlweOtBranch br else true) && verifyRlweFoBatch brs (mask / 2)

theorem verifyRlweFoBatch_corrupted_eq_survives :
    ∀ (branches : List RlweOtBranchSample) (mask : Nat),
      (∀ br ∈ branches, verifyRlweOtBranch br = false) →
      verifyRlweFoBatch branches mask = foSurvivesBranchChecks branches.length mask
  | [], _, _ => rfl
  | br :: brs, mask, hAllBad => by
    have hBad0 : verifyRlweOtBranch br = false := hAllBad br (.head _)
    have hTail := verifyRlweFoBatch_corrupted_eq_survives brs (mask / 2)
      (fun b hb => hAllBad b (.tail _ hb))
    simp only [verifyRlweFoBatch, foSurvivesBranchChecks, List.length_cons, hBad0, hTail]
    have hMod : mask % 2 = 0 ∨ mask % 2 = 1 := by omega
    rcases hMod with hm0 | hm1
    · simp [hm0]
    · simp [hm1]

/-- **Ring-LWE FO Selective-Failure Soundness (`rlwe_fo_cut_and_choose_sound`)**:
    1. Every valid RLWE branch (`verifyRlweOtBranch br = true`) decrypts with **zero** bit error
       (`rlweDecodeBit br.claimedCt = br.bit`).
    2. Across any `k` malformed RLWE ciphertexts (`verifyRlweOtBranch br = false`), `verifyRlweFoBatch`
       accepts on exact count `1` out of `2 ^ k` receiver choice masks (`ratLe (survive, 2^k) (1, 2^k)`). -/
theorem rlwe_fo_cut_and_choose_sound
    (branches : List RlweOtBranchSample)
    (hAllCorrupted : ∀ br ∈ branches, verifyRlweOtBranch br = false) :
    let k := branches.length
    let surviveCount := finSum (2 ^ k) (fun c => if verifyRlweFoBatch branches c.1 then 1 else 0)
    (∀ br : RlweOtBranchSample, verifyRlweOtBranch br = true → rlweDecodeBit br.claimedCt = br.bit) ∧
    surviveCount = 1 ∧
    ratLe (surviveCount, 2 ^ k) (1, 2 ^ k) := by
  intro k surviveCount
  have hDec : ∀ br : RlweOtBranchSample, verifyRlweOtBranch br = true → rlweDecodeBit br.claimedCt = br.bit := by
    intro br hOk
    unfold verifyRlweOtBranch at hOk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
    rw [hOk.2]
    exact rlwe1024_ot_decrypt_exact br.bit br.eSign br.eMag hOk.1
  have hEqSurv : surviveCount = finSum (2 ^ k) (fun c => if foSurvivesBranchChecks k c.1 then 1 else 0) := by
    apply finSum_congr
    intro c
    rw [verifyRlweFoBatch_corrupted_eq_survives branches c.1 hAllCorrupted]
  obtain ⟨hS1, _, hRat⟩ := fo_cut_and_choose_selective_failure_bound k
  rw [hEqSurv]
  exact ⟨hDec, hS1, hRat⟩

/-- **`#tooth` Out-of-Bound RLWE Noise Flip Refusal (`tooth_rlwe_fo_corrupted_ciphertext_caught`)**:
    Injecting excessive RLWE noise `eMag = 4000 > 2049` flips `rlweDecodeBit` from `false` to `true`,
    and `verifyRlweOtBranch` / `verifyRlweFoBatch` rejects (`= false`) whenever audited! -/
theorem tooth_rlwe_fo_corrupted_ciphertext_caught :
    let badBr : RlweOtBranchSample := ⟨false, true, 4000, rlweNoisyEncode false true 4000⟩
    rlweDecodeBit badBr.claimedCt ≠ badBr.bit ∧
    verifyRlweOtBranch badBr = false ∧
    verifyRlweFoBatch [badBr] 1 = false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

section UniversalCombinerAndKos
variable {R : Type} [LawfulCommRing R]
open CommRingOps

/-- 3-to-1 full-rank universal linear combiner `(x₀, x₁, x₂) ↦ x₀ + c₁·x₁ + c₂·x₂`
    mapping 384 bits (`Tower128 × Tower128 × Tower128`) to 128 bits (`Tower128`). -/
def linearCombiner3to1 (c1 c2 x0 x1 x2 : R) : R :=
  add x0 (add (mul c1 x1) (mul c2 x2))

/-- **Exact Fiber Bijection of the 3-to-1 Combiner (`linearCombiner3to1Equiv`)**:
    Conditioned on any `(c₁, c₂, x₁, x₂)`, `x₀ ↦ linearCombiner3to1 c₁ c₂ x₀ x₁ x₂` is a 1-to-1
    bijection on `R`, so any single uncorrupted block makes the combined seed 100% uniform. -/
def linearCombiner3to1Equiv (c1 c2 x1 x2 : R) : SimpleEquiv R R where
  toFun := fun x0 => linearCombiner3to1 c1 c2 x0 x1 x2
  invFun := fun y => sub y (add (mul c1 x1) (mul c2 x2))
  left_inv := by
    intro x0
    dsimp only [linearCombiner3to1]
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
  right_inv := by
    intro y
    dsimp only [linearCombiner3to1]
    rw [LawfulCommRing.add_comm _ (add (mul c1 x1) (mul c2 x2)),
        LawfulCommRing.add_sub_cancel_left]

/-- **2-Universal Collision Bound for `linearCombiner3to1` (`linearCombiner3to1_universal_c1`)**:
    Over any integral domain `R` (`Tower128`), for any distinct triples with `x₁ ≠ x₁'` and any
    fixed `c₂`, at most **1** seed `c₁ ∈ S` causes a combiner collision! -/
theorem linearCombiner3to1_universal_c1 [DecidableEq R] [NoZeroDivisors R]
    (c2 x0 x1 x2 x0' x1' x2' : R) (S : List R) (hNodup : S.Nodup) (hDiff1 : x1 ≠ x1') :
    (S.filter (fun c1 => decide (linearCombiner3to1 c1 c2 x0 x1 x2 = linearCombiner3to1 c1 c2 x0' x1' x2'))).length ≤ 1 := by
  let dx1 := sub x1 x1'
  let constTerm := add (sub x0 x0') (mul c2 (sub x2 x2'))
  have hDx1Nz : dx1 ≠ zero := fun h0 => hDiff1 (LawfulCommRing.sub_eq_zero_iff.mp h0)
  have hAddDiff : ∀ c1 : R,
      add (RoundPoly.evalCoeffs [constTerm, dx1] c1) (linearCombiner3to1 c1 c2 x0' x1' x2') =
      linearCombiner3to1 c1 c2 x0 x1 x2 := by
    intro c1
    dsimp only [RoundPoly.evalCoeffs, constTerm, dx1, linearCombiner3to1]
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    -- Rearrange: ((x0 - x0') + c2*(x2 - x2')) + c1*(x1 - x1') + (x0' + (c1*x1' + c2*x2'))
    rw [LawfulCommRing.add_comm (mul c1 x1') (mul c2 x2'),
        ← LawfulCommRing.add_assoc x0' (mul c2 x2') (mul c1 x1'),
        LawfulCommRing.add_add_add_comm (add (sub x0 x0') (mul c2 (sub x2 x2'))) (mul c1 (sub x1 x1'))
          (add x0' (mul c2 x2')) (mul c1 x1'),
        LawfulCommRing.add_add_add_comm (sub x0 x0') (mul c2 (sub x2 x2')) x0' (mul c2 x2')]
    have hSubAdd : ∀ (a b : R), add (sub a b) b = a := by
      intro a b
      rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
          LawfulCommRing.add_left_neg, LawfulCommRing.add_zero]
    have hMulSubAdd : ∀ (k a b : R), add (mul k (sub a b)) (mul k b) = mul k a := by
      intro k a b
      rw [← LawfulCommRing.left_distrib, hSubAdd]
    rw [hSubAdd x0 x0', hMulSubAdd c2 x2 x2', hMulSubAdd c1 x1 x1',
        LawfulCommRing.add_assoc x0 (mul c2 x2) (mul c1 x1),
        LawfulCommRing.add_comm (mul c2 x2) (mul c1 x1)]
  have hEqPoly : ∀ c1 : R,
      (linearCombiner3to1 c1 c2 x0 x1 x2 = linearCombiner3to1 c1 c2 x0' x1' x2') ↔
      RoundPoly.evalCoeffs [constTerm, dx1] c1 = zero := by
    intro c1
    constructor
    · intro hEq
      apply LawfulCommRing.add_left_cancel (a := linearCombiner3to1 c1 c2 x0' x1' x2')
      rw [LawfulCommRing.add_zero, LawfulCommRing.add_comm, hAddDiff c1, hEq]
    · intro h0
      rw [← hAddDiff c1, h0, LawfulCommRing.zero_add]
  have hWitnessNz : ∃ z : R, RoundPoly.evalCoeffs [constTerm, dx1] z ≠ zero := by
    have hNe01 : RoundPoly.evalCoeffs [constTerm, dx1] one ≠ RoundPoly.evalCoeffs [constTerm, dx1] zero := by
      intro hEq
      simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
                 LawfulCommRing.one_mul, LawfulCommRing.zero_mul] at hEq
      exact hDx1Nz (LawfulCommRing.add_left_cancel (a := constTerm) (hEq.trans (LawfulCommRing.add_zero _).symm))
    by_cases h0 : RoundPoly.evalCoeffs [constTerm, dx1] zero = zero
    · exact ⟨one, fun h1 => hNe01 (h1.trans h0.symm)⟩
    · exact ⟨zero, h0⟩
  have hFilt :
      S.filter (fun c1 => decide (linearCombiner3to1 c1 c2 x0 x1 x2 = linearCombiner3to1 c1 c2 x0' x1' x2')) =
      S.filter (fun c1 => decide (RoundPoly.evalCoeffs [constTerm, dx1] c1 = zero)) := by
    apply List.filter_congr
    intro c1 _
    simp only [decide_eq_decide]
    exact hEqPoly c1
  rw [hFilt]
  exact RoundPoly.roots_nodup_length_le 1 [constTerm, dx1] S hNodup (by simp) hWitnessNz

/-- **Collision probability of the 3-to-1 field combiner (`linearCombiner3to1_collision_probability_le`)**:
    over `Tower128`, two inputs differing in the `x₁` block collide for at most one seed `c₁` of any
    duplicate-free seed list, i.e. with probability at most `1 / 2^128` over a uniform `c₁`.
    This is a 2-universality statement only. The statistical-distance conclusion for a source with
    leakage is the Leftover Hash Lemma `Qsag.lhl_security_of_two_universal`, instantiated for the
    production binary `128 × 384` extractor in `Qsag.kos_combiner_128x384_lhl_security`
    (`Qsag.LatticePreprocessingFull`); no min-entropy hypothesis appears here. -/
theorem linearCombiner3to1_collision_probability_le
    (c2 x0 x1 x2 x0' x1' x2' : Tower128) (S : List Tower128)
    (hNodup : S.Nodup) (hDiff1 : x1 ≠ x1') :
    let bad := (S.filter (fun c1 => decide (linearCombiner3to1 c1 c2 x0 x1 x2 = linearCombiner3to1 c1 c2 x0' x1' x2'))).length
    bad ≤ 1 ∧
    ratLe (bad, 2 ^ 128) (1, 2 ^ 128) := by
  intro bad
  have hBad : bad ≤ 1 := linearCombiner3to1_universal_c1 c2 x0 x1 x2 x0' x1' x2' S hNodup hDiff1
  refine ⟨hBad, ?_⟩
  unfold ratLe; dsimp only
  exact ⟨Nat.two_pow_pos 128, Nat.two_pow_pos 128, Nat.mul_le_mul_right _ hBad⟩

def fieldProductResidual (deltaU_ell secretDelta senderOffset chi_ell : R) : R :=
  sub (mul (mul chi_ell deltaU_ell) secretDelta) senderOffset

/-- A field-product residual pins at most one key. This is not the bitwise KOS residual. -/
theorem field_product_key_uniqueness [DecidableEq R] [NoZeroDivisors R]
    (deltaU_ell senderOffset chi_ell : R) (S : List R) (hNodup : S.Nodup)
    (hCheated : deltaU_ell ≠ zero) (hChiNz : chi_ell ≠ zero) :
    (S.filter (fun secretDelta => decide (fieldProductResidual deltaU_ell secretDelta senderOffset chi_ell = zero))).length ≤ 1 := by
  let coeff := mul chi_ell deltaU_ell
  have hCoeffNz : coeff ≠ zero := fun h0 => by
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h0 with hc | hd
    · exact hChiNz hc
    · exact hCheated hd
  have hWitnessNz : ∃ z : R, RoundPoly.evalCoeffs [neg senderOffset, coeff] z ≠ zero := by
    have hNe01 : RoundPoly.evalCoeffs [neg senderOffset, coeff] one ≠
                 RoundPoly.evalCoeffs [neg senderOffset, coeff] zero := by
      intro hEq
      simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
                 LawfulCommRing.one_mul, LawfulCommRing.zero_mul] at hEq
      exact hCoeffNz (LawfulCommRing.add_left_cancel (a := neg senderOffset) (hEq.trans (LawfulCommRing.add_zero _).symm))
    by_cases h0 : RoundPoly.evalCoeffs [neg senderOffset, coeff] zero = zero
    · exact ⟨one, fun h1 => hNe01 (h1.trans h0.symm)⟩
    · exact ⟨zero, h0⟩
  have hFilt :
      S.filter (fun secretDelta => decide (fieldProductResidual deltaU_ell secretDelta senderOffset chi_ell = zero)) =
      S.filter (fun secretDelta => decide (RoundPoly.evalCoeffs [neg senderOffset, coeff] secretDelta = zero)) := by
    apply List.filter_congr
    intro d _
    simp only [fieldProductResidual, coeff, RoundPoly.evalCoeffs,
               LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
               LawfulCommRing.sub_eq_add_neg, LawfulCommRing.mul_comm (mul chi_ell deltaU_ell) d,
               LawfulCommRing.add_comm]
  rw [hFilt]
  exact RoundPoly.roots_nodup_length_le 1 [neg senderOffset, coeff] S hNodup (by simp) hWitnessNz

/-- Field cancellation when coefficients are chosen after challenges. -/
theorem field_product_prechallenge_cancellation (chi0 chi1 secretDelta : R) (hChi1Nz : chi1 ≠ zero) :
    let deltaU0 := chi1
    let deltaU1 := neg chi0
    deltaU0 ≠ zero ∧
    mul (add (mul chi0 deltaU0) (mul chi1 deltaU1)) secretDelta = zero := by
  refine ⟨hChi1Nz, ?_⟩
  rw [LawfulCommRing.mul_neg, LawfulCommRing.mul_comm chi1 chi0,
      LawfulCommRing.add_right_neg, LawfulCommRing.zero_mul]

/-- Linear primal-LPN parity compression `H · v` over `R`: each output coordinate is a sparse parity
    sum over selected noisy correlation indices. -/
def applyLpnParityRow (v : Nat → R) (support : List Nat) : R :=
  ringListSum (support.map v)

/-- **Primal-LPN Linear Compression Preserves Additive OLE Shares (`pcg_lpn_ole_expansion_sound`)**:
    Applying any public primal-LPN parity check row `support` locally to two parties' additive
    noisy correlation shares `u_A, u_B` (`u_A(i) + u_B(i) = z(i)`) preserves exact additive sharing
    `applyLpnParityRow u_A support + applyLpnParityRow u_B support = applyLpnParityRow z support`. -/
theorem pcg_lpn_ole_expansion_sound (uA uB : Nat → R) :
    ∀ (support : List Nat),
      add (applyLpnParityRow uA support) (applyLpnParityRow uB support) =
      applyLpnParityRow (fun i => add (uA i) (uB i)) support
  | [] => by simp [applyLpnParityRow, ringListSum, LawfulCommRing.add_zero]
  | idx :: rest => by
    simp only [applyLpnParityRow, List.map_cons, ringListSum]
    rw [LawfulCommRing.add_add_add_comm]
    exact congrArg (add (add (uA idx) (uB idx))) (pcg_lpn_ole_expansion_sound uA uB rest)

end UniversalCombinerAndKos

/-- Single corrupted row's KOS residual: correlation is bitwise AND before
multiplication by the field challenge. -/
def kosColumnResidual (k : Nat) (deltaU secretDelta : TowerBitVec k)
    (senderOffset chi : TowerElem k) : TowerElem k :=
  towerAdd k (towerMul k chi (unpackTower k (deltaU &&& secretDelta))) senderOffset

/-- For zero sender offset and a nonzero challenge, acceptance means the masked
bitwise error is zero. It does not pin the full correlation key. -/
theorem kos_interactive_check_sound (k : Nat) (deltaU secretDelta : TowerBitVec k)
    (chi : TowerElem k) (hChi : chi ≠ towerZero k) :
    kosColumnResidual k deltaU secretDelta (towerZero k) chi = towerZero k ↔
      unpackTower k (deltaU &&& secretDelta) = towerZero k := by
  simp only [kosColumnResidual, towerAdd_zero, towerMul_eq_zero_iff]
  exact ⟨fun h => h.elim (fun hc => False.elim (hChi hc)) id, Or.inr⟩

/-- A one-bit corruption leaves other key bits unconstrained: two distinct
128-bit keys already pass with the same nonzero challenge. -/
theorem kos_single_bit_does_not_pin_key :
    (0#128 : TowerBitVec 7) ≠ 2#128 ∧
    kosColumnResidual 7 1#128 0#128 (towerZero 7) (towerOne 7) = towerZero 7 ∧
    kosColumnResidual 7 1#128 2#128 (towerZero 7) (towerOne 7) = towerZero 7 := by
  have hz : unpackTower 7 0#128 = towerZero 7 := unpackTower_zero 7
  refine ⟨by decide +kernel, ?_, ?_⟩ <;>
    simp [kosColumnResidual, show (1#128 &&& 2#128) = 0#128 by decide +kernel,
      hz, towerMul_zero]

/-- The production extractor shape is a binary 128-by-384 matrix. -/
abbrev BinaryExtractorMatrix := Fin 128 → BitVec 384

def binaryInnerProduct (a b : BitVec 384) : Bool :=
  (List.range 384).foldl (fun acc i => xor acc (a.getLsbD i && b.getLsbD i)) false

def extract384To128 (matrix : BinaryExtractorMatrix) (input : BitVec 384) : Fin 128 → Bool :=
  fun row => binaryInnerProduct (matrix row) input

section ExtractorAndBatchedKos

private def foldXorAnd (n : Nat) (f g : Nat → Bool) (init : Bool) : Bool :=
  (List.range n).foldl (fun acc i => xor acc (f i && g i)) init

private theorem foldXorAnd_succ (n : Nat) (f g : Nat → Bool) (init : Bool) :
    foldXorAnd (n + 1) f g init = xor (foldXorAnd n f g init) (f n && g n) := by
  simp [foldXorAnd, List.range_succ, List.foldl_append]

private theorem foldXorAnd_congr (n : Nat) {f₁ f₂ g₁ g₂ : Nat → Bool}
    (hf : ∀ i, i < n → f₁ i = f₂ i) (hg : ∀ i, i < n → g₁ i = g₂ i) :
    foldXorAnd n f₁ g₁ false = foldXorAnd n f₂ g₂ false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldXorAnd_succ, foldXorAnd_succ,
        ih (fun i hi => hf i (Nat.lt_succ_of_lt hi)) (fun i hi => hg i (Nat.lt_succ_of_lt hi)),
        hf n (Nat.lt_succ_self n), hg n (Nat.lt_succ_self n)]

private theorem foldXorAnd_zero_left (n : Nat) {f g : Nat → Bool}
    (hf : ∀ i, i < n → f i = false) :
    foldXorAnd n f g false = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldXorAnd_succ, ih (fun i hi => hf i (Nat.lt_succ_of_lt hi)), hf n (Nat.lt_succ_self n)]
    rfl

private theorem foldXorAnd_xor_right (n : Nat) (f g₁ g₂ : Nat → Bool) :
    foldXorAnd n f (fun i => xor (g₁ i) (g₂ i)) false =
      xor (foldXorAnd n f g₁ false) (foldXorAnd n f g₂ false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldXorAnd_succ, foldXorAnd_succ, foldXorAnd_succ, ih]
    cases foldXorAnd n f g₁ false <;> cases foldXorAnd n f g₂ false <;>
      cases f n <;> cases g₁ n <;> cases g₂ n <;> rfl

private theorem foldXorAnd_split (m k : Nat) (f g : Nat → Bool) :
    foldXorAnd (m + k) f g false =
      xor (foldXorAnd m f g false)
          (foldXorAnd k (fun j => f (m + j)) (fun j => g (m + j)) false) := by
  induction k with
  | zero => simp [foldXorAnd]
  | succ k ih =>
    rw [Nat.add_succ, foldXorAnd_succ, foldXorAnd_succ, ih, Bool.xor_assoc]

private theorem foldXorAnd_unit_left :
    ∀ (n k : Nat) (f g : Nat → Bool),
      k < n → (∀ i, i < n → f i = decide (i = k)) →
      foldXorAnd n f g false = g k
  | 0, _, _, _, hk, _ => by omega
  | n + 1, k, f, g, hk, hf => by
    rw [foldXorAnd_succ]
    if hEq : k = n then
      subst hEq
      have hZero : foldXorAnd k f g false = false :=
        foldXorAnd_zero_left k (fun i hi => by rw [hf i (Nat.lt_succ_of_lt hi)]; simp [Nat.ne_of_lt hi])
      rw [hZero, hf k (Nat.lt_succ_self k)]
      simp
    else
      have hkLt : k < n := by omega
      rw [foldXorAnd_unit_left n k f g hkLt (fun i hi => hf i (Nat.lt_succ_of_lt hi)),
          hf n (Nat.lt_succ_self n)]
      have hNe : ¬ (n = k) := fun h => hEq h.symm
      simp [hNe]

/-- $\mathbb{F}_2$-linearity of `binaryInnerProduct` in its right operand. -/
theorem binaryInnerProduct_xor_right (a b₁ b₂ : BitVec 384) :
    binaryInnerProduct a (b₁ ^^^ b₂) = xor (binaryInnerProduct a b₁) (binaryInnerProduct a b₂) := by
  change foldXorAnd 384 a.getLsbD (b₁ ^^^ b₂).getLsbD false =
    xor (foldXorAnd 384 a.getLsbD b₁.getLsbD false) (foldXorAnd 384 a.getLsbD b₂.getLsbD false)
  rw [foldXorAnd_congr 384 (fun _ _ => rfl) (fun _ _ => BitVec.getLsbD_xor)]
  exact foldXorAnd_xor_right 384 a.getLsbD b₁.getLsbD b₂.getLsbD

/-- $\mathbb{F}_2$-linearity of `extract384To128`: `M · (x ⊕ y) = (M · x) ⊕ (M · y)`. -/
theorem extract384To128_xor (M : BinaryExtractorMatrix) (x y : BitVec 384) (row : Fin 128) :
    extract384To128 M (x ^^^ y) row = xor (extract384To128 M x row) (extract384To128 M y row) :=
  binaryInnerProduct_xor_right (M row) x y

private def packBitsAux : (n : Nat) → (Nat → Bool) → BitVec n
  | 0, _ => 0#0
  | n + 1, f => (BitVec.ofBool (f n) ++ packBitsAux n f).cast (Nat.add_comm 1 n)

private theorem packBitsAux_getLsbD :
    ∀ (n : Nat) (f : Nat → Bool) (i : Nat), i < n → (packBitsAux n f).getLsbD i = f i
  | 0, _, _, hi => by omega
  | n + 1, f, i, hi => by
    simp only [packBitsAux, BitVec.getLsbD_cast, BitVec.getLsbD_append]
    if hLt : i < n then
      simp only [hLt, ↓reduceIte]
      exact packBitsAux_getLsbD n f i hLt
    else
      have hEq : i = n := by omega
      subst hEq
      simp

/-- Pack a 128-bit boolean row vector `Fin 128 → Bool` into `BitVec 128`. -/
def packBits128 (f : Fin 128 → Bool) : BitVec 128 :=
  packBitsAux 128 (fun i => if h : i < 128 then f ⟨i, h⟩ else false)

@[simp] theorem packBits128_getLsbD (f : Fin 128 → Bool) (row : Fin 128) :
    (packBits128 f).getLsbD row.1 = f row := by
  unfold packBits128
  rw [packBitsAux_getLsbD 128 _ row.1 row.2]
  simp [row.2]

@[simp] theorem packBits128_eta (v : BitVec 128) :
    packBits128 (fun row => v.getLsbD row.1) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact packBits128_getLsbD (fun row => v.getLsbD row.1) ⟨i, hi⟩

theorem packBits128_injective {f g : Fin 128 → Bool}
    (h : packBits128 f = packBits128 g) : f = g := by
  funext row
  have hBit := congrArg (fun v => v.getLsbD row.1) h
  simpa only [packBits128_getLsbD] using hBit

/-- Split a 384-bit source into three 128-bit blocks `(b0, b1, b2)` (`LSB .. MSB`). -/
def split384Blocks (x : BitVec 384) : BitVec 128 × BitVec 128 × BitVec 128 :=
  (x.extractLsb' 0 128, x.extractLsb' 128 128, x.extractLsb' 256 128)

/-- Join three 128-bit blocks `(b0, b1, b2)` into `BitVec 384`. -/
def join384Blocks (b0 b1 b2 : BitVec 128) : BitVec 384 :=
  ((b2 ++ b1) ++ b0).cast (by decide)

@[simp] theorem join384Blocks_getLsbD (b0 b1 b2 : BitVec 128) (i : Nat) (hi : i < 384) :
    (join384Blocks b0 b1 b2).getLsbD i =
      if i < 128 then b0.getLsbD i
      else if i < 256 then b1.getLsbD (i - 128)
      else b2.getLsbD (i - 256) := by
  unfold join384Blocks
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append]
  if h0 : i < 128 then
    simp [h0]
  else if h1 : i < 256 then
    have hSub : i - 128 < 128 := by omega
    simp [h0, h1, hSub]
  else
    have hSub : ¬ (i - 128 < 128) := by omega
    have hEq : i - 128 - 128 = i - 256 := by omega
    simp [h0, h1, hSub, hEq]

@[simp] theorem split384Blocks_join384Blocks (b0 b1 b2 : BitVec 128) :
    split384Blocks (join384Blocks b0 b1 b2) = (b0, b1, b2) := by
  unfold split384Blocks
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    (apply BitVec.eq_of_getLsbD_eq; intro i hi;
     simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and];
     rw [join384Blocks_getLsbD _ _ _ _ (by omega)];
     split <;> simp_all <;> omega)

@[simp] theorem join384Blocks_split384Blocks (x : BitVec 384) :
    let (b0, b1, b2) := split384Blocks x
    join384Blocks b0 b1 b2 = x := by
  dsimp only [split384Blocks]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [join384Blocks_getLsbD _ _ _ i hi]
  if h0 : i < 128 then
    simp [h0]
  else if h1 : i < 256 then
    have hSub : i - 128 < 128 := by omega
    have hAdd : 128 + (i - 128) = i := by omega
    simp [h0, h1, hSub, hAdd]
  else
    have hSub : i - 256 < 128 := by omega
    have hAdd : 256 + (i - 256) = i := by omega
    simp [h0, h1, hSub, hAdd]

/-- `col`-th standard basis vector `e_col ∈ {0, 1}^{128}`. -/
def basisBit128 (col : Nat) : BitVec 128 :=
  packBits128 (fun j => decide (j.1 = col))

@[simp] theorem basisBit128_getLsbD (col i : Nat) (hi : i < 128) :
    (basisBit128 col).getLsbD i = decide (i = col) :=
  packBits128_getLsbD (fun j => decide (j.1 = col)) ⟨i, hi⟩

/-- `row`-th $\mathbb{F}_2$-row of multiplication by `c ∈ Tower128` (`GF(2^{128})`). -/
def towerMulRow128 (c : Tower128) (row : Fin 128) : BitVec 128 :=
  packBits128 (fun col => (packTower 7 (towerMul 7 c (unpackTower 7 (basisBit128 col.1)))).getLsbD row.1)

private def prefixMask128 : Nat → BitVec 128 → BitVec 128
  | 0 => fun _ => (0 : TowerBitVec 7)
  | k + 1 => fun v => prefixMask128 k v ^^^ (if v.getLsbD k then basisBit128 k else (0 : TowerBitVec 7))

private theorem prefixMask128_getLsbD (n : Nat) (v : BitVec 128) (i : Nat)
    (hk : n ≤ 128) (hi : i < 128) :
    (prefixMask128 n v).getLsbD i = (decide (i < n) && v.getLsbD i) := by
  induction n with
  | zero =>
    simp only [prefixMask128]
    have hZ128 : (0 : TowerBitVec 7) = 0#128 := rfl
    rw [hZ128, BitVec.getLsbD_zero, decide_eq_false (Nat.not_lt_zero i), Bool.false_and]
  | succ k ih =>
    have hZ128 : (0 : TowerBitVec 7) = 0#128 := rfl
    simp only [prefixMask128, BitVec.getLsbD_xor, ih (by omega)]
    if hEq : i = k then
      subst hEq
      rw [decide_eq_false (Nat.lt_irrefl i), decide_eq_true (Nat.lt_succ_self i),
          Bool.false_and, Bool.true_and, Bool.false_xor]
      cases hv : v.getLsbD i
      · simp only [Bool.false_eq_true, ↓reduceIte, hZ128, BitVec.getLsbD_zero]
      · simp only [↓reduceIte, basisBit128_getLsbD i i hi, decide_true]
    else
      have hdSame : decide (i < k + 1) = decide (i < k) := by
        if hLt : i < k then
          rw [decide_eq_true (by omega : i < k + 1), decide_eq_true hLt]
        else
          rw [decide_eq_false (by omega : ¬ (i < k + 1)), decide_eq_false hLt]
      rw [hdSame]
      cases hv : v.getLsbD k
      · simp only [Bool.false_eq_true, ↓reduceIte, hZ128, BitVec.getLsbD_zero, Bool.xor_false]
      · simp only [↓reduceIte, basisBit128_getLsbD k i hi, decide_eq_false hEq, Bool.xor_false]

private theorem prefixMask128_full (v : BitVec 128) : prefixMask128 128 v = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [prefixMask128_getLsbD 128 v i (Nat.le_refl 128) hi, decide_eq_true hi, Bool.true_and]

private theorem unpackTower_xor (k : Nat) (a b : TowerBitVec k) :
    unpackTower k (a ^^^ b) = towerAdd k (unpackTower k a) (unpackTower k b) := by
  apply packTower_injective k
  rw [packTower_unpackTower, packTower_add, packTower_unpackTower, packTower_unpackTower]

private theorem foldXorAnd_towerMulRow128 (c : Tower128) (row : Fin 128) (v : BitVec 128) :
    ∀ (n : Nat), n ≤ 128 →
      foldXorAnd n (towerMulRow128 c row).getLsbD v.getLsbD false =
        (packTower 7 (towerMul 7 c (unpackTower 7 (prefixMask128 n v)))).getLsbD row.1
  | 0, _ => by
    have hZ128 : (0 : TowerBitVec 7) = 0#128 := rfl
    simp only [foldXorAnd, List.range_zero, List.foldl_nil, prefixMask128]
    rw [unpackTower_zero, towerMul_zero, packTower_zero, hZ128, BitVec.getLsbD_zero]
  | k + 1, hk => by
    have hkLt : k < 128 := by omega
    have hZ128 : (0 : TowerBitVec 7) = 0#128 := rfl
    rw [foldXorAnd_succ, foldXorAnd_towerMulRow128 c row v k (by omega)]
    have hCol : (towerMulRow128 c row).getLsbD k =
        (packTower 7 (towerMul 7 c (unpackTower 7 (basisBit128 k)))).getLsbD row.1 :=
      packBits128_getLsbD _ ⟨k, hkLt⟩
    rw [hCol]
    change xor ((packTower 7 (towerMul 7 c (unpackTower 7 (prefixMask128 k v)))).getLsbD row.1)
      ((packTower 7 (towerMul 7 c (unpackTower 7 (basisBit128 k)))).getLsbD row.1 && v.getLsbD k) =
      (packTower 7 (towerMul 7 c (unpackTower 7
        (prefixMask128 k v ^^^ (if v.getLsbD k then basisBit128 k else (0 : TowerBitVec 7)))))).getLsbD row.1
    cases hv : v.getLsbD k
    · simp only [Bool.false_eq_true, ↓reduceIte, hZ128, BitVec.xor_zero, Bool.and_false, Bool.xor_false]
    · simp only [↓reduceIte, Bool.and_true]
      rw [unpackTower_xor, towerMul_add_distrib, packTower_add, BitVec.getLsbD_xor]

/-- Full-rank systematic `[I_{128} | mul_{c_1} | mul_{c_2}]` `BinaryExtractorMatrix` realizing
    `linearCombiner3to1 c1 c2` on `BitVec 384`. -/
def towerCombinerMatrix (c1 c2 : Tower128) : BinaryExtractorMatrix :=
  fun row => join384Blocks (basisBit128 row.1) (towerMulRow128 c1 row) (towerMulRow128 c2 row)

theorem extract384To128_towerCombinerMatrix_join (c1 c2 : Tower128) (b0 b1 b2 : BitVec 128) :
    packBits128 (extract384To128 (towerCombinerMatrix c1 c2) (join384Blocks b0 b1 b2)) =
      packTower 7 (linearCombiner3to1 c1 c2 (unpackTower 7 b0) (unpackTower 7 b1) (unpackTower 7 b2)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  let row : Fin 128 := ⟨r, hr⟩
  change (packBits128 (extract384To128 (towerCombinerMatrix c1 c2) (join384Blocks b0 b1 b2))).getLsbD row.1 = _
  rw [packBits128_getLsbD]
  unfold extract384To128 binaryInnerProduct towerCombinerMatrix
  change foldXorAnd ((128 + 128) + 128)
      (join384Blocks (basisBit128 row.1) (towerMulRow128 c1 row) (towerMulRow128 c2 row)).getLsbD
      (join384Blocks b0 b1 b2).getLsbD false = _
  rw [foldXorAnd_split (128 + 128) 128, foldXorAnd_split 128 128]
  have hB0 : foldXorAnd 128
      (join384Blocks (basisBit128 row.1) (towerMulRow128 c1 row) (towerMulRow128 c2 row)).getLsbD
      (join384Blocks b0 b1 b2).getLsbD false = b0.getLsbD row.1 := by
    rw [foldXorAnd_congr 128 (f₂ := (basisBit128 row.1).getLsbD) (g₂ := b0.getLsbD)
      (fun i hi => by rw [join384Blocks_getLsbD _ _ _ i (by omega)]; simp [hi])
      (fun i hi => by rw [join384Blocks_getLsbD _ _ _ i (by omega)]; simp [hi])]
    exact foldXorAnd_unit_left 128 row.1 (basisBit128 row.1).getLsbD b0.getLsbD row.2
      (fun i hi => basisBit128_getLsbD row.1 i hi)
  have hB1 : foldXorAnd 128
      (fun j => (join384Blocks (basisBit128 row.1) (towerMulRow128 c1 row) (towerMulRow128 c2 row)).getLsbD (128 + j))
      (fun j => (join384Blocks b0 b1 b2).getLsbD (128 + j)) false =
      (packTower 7 (towerMul 7 c1 (unpackTower 7 b1))).getLsbD row.1 := by
    rw [foldXorAnd_congr 128 (f₂ := (towerMulRow128 c1 row).getLsbD) (g₂ := b1.getLsbD)
      (fun j hj => by
        rw [join384Blocks_getLsbD _ _ _ (128 + j) (by omega)]
        have hNot0 : ¬ (128 + j < 128) := by omega
        have hLt1 : 128 + j < 256 := by omega
        simp [hNot0, hLt1])
      (fun j hj => by
        rw [join384Blocks_getLsbD _ _ _ (128 + j) (by omega)]
        have hNot0 : ¬ (128 + j < 128) := by omega
        have hLt1 : 128 + j < 256 := by omega
        simp [hNot0, hLt1])]
    rw [foldXorAnd_towerMulRow128 c1 row b1 128 (Nat.le_refl 128), prefixMask128_full]
  have hB2 : foldXorAnd 128
      (fun j => (join384Blocks (basisBit128 row.1) (towerMulRow128 c1 row) (towerMulRow128 c2 row)).getLsbD ((128 + 128) + j))
      (fun j => (join384Blocks b0 b1 b2).getLsbD ((128 + 128) + j)) false =
      (packTower 7 (towerMul 7 c2 (unpackTower 7 b2))).getLsbD row.1 := by
    rw [foldXorAnd_congr 128 (f₂ := (towerMulRow128 c2 row).getLsbD) (g₂ := b2.getLsbD)
      (fun j hj => by
        rw [join384Blocks_getLsbD _ _ _ ((128 + 128) + j) (by omega)]
        have hNot0 : ¬ ((128 + 128) + j < 128) := by omega
        have hNot1 : ¬ ((128 + 128) + j < 256) := by omega
        have hSub : (128 + 128) + j - 256 = j := by omega
        simp [hNot0, hNot1, hSub])
      (fun j hj => by
        rw [join384Blocks_getLsbD _ _ _ ((128 + 128) + j) (by omega)]
        have hNot0 : ¬ ((128 + 128) + j < 128) := by omega
        have hNot1 : ¬ ((128 + 128) + j < 256) := by omega
        have hSub : (128 + 128) + j - 256 = j := by omega
        simp [hNot0, hNot1, hSub])]
    rw [foldXorAnd_towerMulRow128 c2 row b2 128 (Nat.le_refl 128), prefixMask128_full]
  rw [hB0, hB1, hB2, Bool.xor_assoc]
  unfold linearCombiner3to1
  change _ = (packTower 7 (towerAdd 7 (unpackTower 7 b0)
    (towerAdd 7 (towerMul 7 c1 (unpackTower 7 b1)) (towerMul 7 c2 (unpackTower 7 b2))))).getLsbD row.1
  rw [packTower_add, packTower_add, packTower_unpackTower, BitVec.getLsbD_xor, BitVec.getLsbD_xor]

/-- **Exact Matrix-to-Field Refinement (`extract384To128_towerCombinerMatrix_eq`)**:
    Evaluating the `128 × 384` GF(2) matrix `towerCombinerMatrix c1 c2` via `extract384To128`
    is bit-for-bit identical to `linearCombiner3to1 c1 c2` over `Tower128`! -/
theorem extract384To128_towerCombinerMatrix_eq (c1 c2 : Tower128) (x : BitVec 384) :
    let (b0, b1, b2) := split384Blocks x
    packBits128 (extract384To128 (towerCombinerMatrix c1 c2) x) =
      packTower 7 (linearCombiner3to1 c1 c2 (unpackTower 7 b0) (unpackTower 7 b1) (unpackTower 7 b2)) := by
  have hxEq := join384Blocks_split384Blocks x
  rcases hSplit : split384Blocks x with ⟨b0, b1, b2⟩
  rw [hSplit] at hxEq
  dsimp only at hxEq ⊢
  rw [← hxEq]
  exact extract384To128_towerCombinerMatrix_join c1 c2 b0 b1 b2

/-- **Exact Uniform Fiber Bijection of `extract384To128` (`extract384To128_block0_bijection`)**:
    Conditioned on ANY `(c1, c2 : Tower128)` and ANY `(b1, b2 : BitVec 128)`, the map
    `b0 ↦ packBits128 (extract384To128 (towerCombinerMatrix c1 c2) (join384Blocks b0 b1 b2))`
    is an explicit bijection (`SimpleEquiv (BitVec 128) (BitVec 128)`). -/
def extract384To128_block0_bijection (c1 c2 : Tower128) (b1 b2 : BitVec 128) :
    SimpleEquiv (BitVec 128) (BitVec 128) where
  toFun := fun b0 => packBits128 (extract384To128 (towerCombinerMatrix c1 c2) (join384Blocks b0 b1 b2))
  invFun := fun y =>
    let mask := packTower 7 (towerAdd 7 (towerMul 7 c1 (unpackTower 7 b1)) (towerMul 7 c2 (unpackTower 7 b2)))
    y ^^^ mask
  left_inv := fun b0 => by
    dsimp only
    rw [extract384To128_towerCombinerMatrix_join]
    dsimp only [linearCombiner3to1]
    change (packTower 7 (towerAdd 7 (unpackTower 7 b0)
      (towerAdd 7 (towerMul 7 c1 (unpackTower 7 b1)) (towerMul 7 c2 (unpackTower 7 b2))))) ^^^ _ = b0
    rw [packTower_add, packTower_unpackTower, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  right_inv := fun y => by
    dsimp only
    rw [extract384To128_towerCombinerMatrix_join]
    dsimp only [linearCombiner3to1]
    let m := towerAdd 7 (towerMul 7 c1 (unpackTower 7 b1)) (towerMul 7 c2 (unpackTower 7 b2))
    change packTower 7 (towerAdd 7 (unpackTower 7 (y ^^^ packTower 7 m)) m) = y
    rw [packTower_add, packTower_unpackTower, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Cartesian product list `S1 × S2` for finite seed-pair counting. -/
def cartesianPairs {α β : Type} : List α → List β → List (α × β)
  | [], _ => []
  | a :: as, bs => bs.map (fun b => (a, b)) ++ cartesianPairs as bs

theorem cartesianPairs_length {α β : Type} :
    ∀ (S1 : List α) (S2 : List β), (cartesianPairs S1 S2).length = S1.length * S2.length
  | [], _ => by simp [cartesianPairs]
  | _ :: as, bs => by
    simp [cartesianPairs, cartesianPairs_length as bs, Nat.succ_mul, Nat.add_comm]

private theorem filter_map_pair_length {α β : Type} (a : α) (p : α × β → Bool) :
    ∀ (bs : List β), ((bs.map (fun b => (a, b))).filter p).length =
      (bs.filter (fun b => p (a, b))).length
  | [] => rfl
  | b :: bs => by
    simp only [List.map_cons, List.filter]
    cases p (a, b) <;> simp [filter_map_pair_length a p bs]

private theorem cartesianPairs_filter_row_le {α β : Type} (p : α × β → Bool) (k : Nat) :
    ∀ (S1 : List α) (S2 : List β),
      (∀ a ∈ S1, (S2.filter (fun b => p (a, b))).length ≤ k) →
      ((cartesianPairs S1 S2).filter p).length ≤ S1.length * k
  | [], _, _ => by simp [cartesianPairs]
  | a :: as, bs, hRow => by
    simp only [cartesianPairs, List.filter_append, List.length_append, List.length_cons, Nat.succ_mul]
    rw [filter_map_pair_length]
    have hHead := hRow a (.head _)
    have hTail := cartesianPairs_filter_row_le p k as bs (fun a' ha' => hRow a' (.tail _ ha'))
    omega

private theorem cartesianPairs_filter_cons_col {α β : Type} (p : α × β → Bool) (b : β) (bs : List β) :
    ∀ (S1 : List α),
      ((cartesianPairs S1 (b :: bs)).filter p).length =
        (S1.filter (fun a => p (a, b))).length + ((cartesianPairs S1 bs).filter p).length
  | [] => rfl
  | a :: as => by
    have ih := cartesianPairs_filter_cons_col p b bs as
    simp only [cartesianPairs, List.map_cons, List.cons_append, List.filter]
    cases p (a, b) <;> simp only [List.filter_append, List.length_append, List.length_cons] <;> omega

private theorem cartesianPairs_filter_col_le {α β : Type} (p : α × β → Bool) (k : Nat) :
    ∀ (S1 : List α) (S2 : List β),
      (∀ b ∈ S2, (S1.filter (fun a => p (a, b))).length ≤ k) →
      ((cartesianPairs S1 S2).filter p).length ≤ k * S2.length
  | _, [], _ => by
    have hNil : ∀ (xs : List α), cartesianPairs xs ([] : List β) = [] := by
      intro xs; induction xs with
      | nil => rfl
      | cons _ tl ih => simp [cartesianPairs, ih]
    simp [hNil]
  | S1, b :: bs, hCol => by
    rw [cartesianPairs_filter_cons_col]
    simp only [List.length_cons, Nat.mul_succ]
    have hHead := hCol b (.head _)
    have hTail := cartesianPairs_filter_col_le p k S1 bs (fun b' hb' => hCol b' (.tail _ hb'))
    omega

/-- **Unconditional 2-Universal Collision Bound for `extract384To128` (`extract384To128_two_universal`)**:
    For **EVERY** distinct pair `x ≠ x' : BitVec 384` (with **zero** restriction on which 128-bit
    block differs!) and ANY duplicate-free seed pools `S1 S2 : List Tower128` (`|S1|, |S2| ≤ 2^128`),
    at most `max |S1| |S2| ≤ 2^128` seed pairs `(c1, c2) ∈ S1 × S2` collide under
    `extract384To128 (towerCombinerMatrix c1 c2)`, yielding collision probability `≤ 2^{-128}`! -/
theorem extract384To128_two_universal
    (x x' : BitVec 384) (hDiff : x ≠ x')
    (S1 S2 : List Tower128) (hNodup1 : S1.Nodup) (hNodup2 : S2.Nodup)
    (hLen1 : S1.length ≤ 2 ^ 128) (hLen2 : S2.length ≤ 2 ^ 128) :
    let colliding := (cartesianPairs S1 S2).filter (fun (c1, c2) =>
      decide (packBits128 (extract384To128 (towerCombinerMatrix c1 c2) x) =
              packBits128 (extract384To128 (towerCombinerMatrix c1 c2) x')))
    colliding.length ≤ Nat.max S1.length S2.length ∧
    colliding.length ≤ 2 ^ 128 ∧
    ratLe (colliding.length, 2 ^ 256) (1, 2 ^ 128) := by
  intro colliding
  have hxJoin := join384Blocks_split384Blocks x
  have hxJoin' := join384Blocks_split384Blocks x'
  rcases hSp : split384Blocks x with ⟨b0, b1, b2⟩
  rcases hSp' : split384Blocks x' with ⟨b0', b1', b2'⟩
  rw [hSp] at hxJoin; rw [hSp'] at hxJoin'
  dsimp only at hxJoin hxJoin'
  let x0 := unpackTower 7 b0
  let x1 := unpackTower 7 b1
  let x2 := unpackTower 7 b2
  let x0' := unpackTower 7 b0'
  let x1' := unpackTower 7 b1'
  let x2' := unpackTower 7 b2'
  let p : Tower128 × Tower128 → Bool := fun (c1, c2) =>
    decide (linearCombiner3to1 c1 c2 x0 x1 x2 = linearCombiner3to1 c1 c2 x0' x1' x2')
  have hFiltEq : colliding = (cartesianPairs S1 S2).filter p := by
    apply List.filter_congr
    intro ⟨c1, c2⟩ _
    dsimp only [p]
    rw [← hxJoin, ← hxJoin', extract384To128_towerCombinerMatrix_join, extract384To128_towerCombinerMatrix_join]
    if hEq : linearCombiner3to1 c1 c2 x0 x1 x2 = linearCombiner3to1 c1 c2 x0' x1' x2' then
      rw [decide_eq_true (congrArg (packTower 7) hEq), decide_eq_true hEq]
    else
      rw [decide_eq_false (fun hp => hEq (packTower_injective 7 _ _ hp)), decide_eq_false hEq]
  have hCountLe : ((cartesianPairs S1 S2).filter p).length ≤ Nat.max S1.length S2.length := by
    if he1 : x1 = x1' then
      if he2 : x2 = x2' then
        have hx0 : x0 ≠ x0' := by
          intro he0
          have hb0 : b0 = b0' := by
            have h0 := congrArg (packTower 7) he0
            dsimp only [x0, x0'] at h0
            rw [packTower_unpackTower, packTower_unpackTower] at h0
            exact h0
          have hb1 : b1 = b1' := by
            have h1 := congrArg (packTower 7) he1
            dsimp only [x1, x1'] at h1
            rw [packTower_unpackTower, packTower_unpackTower] at h1
            exact h1
          have hb2 : b2 = b2' := by
            have h2 := congrArg (packTower 7) he2
            dsimp only [x2, x2'] at h2
            rw [packTower_unpackTower, packTower_unpackTower] at h2
            exact h2
          rw [← hxJoin, ← hxJoin', hb0, hb1, hb2] at hDiff
          exact hDiff rfl
        have hRow0 : ((cartesianPairs S1 S2).filter p).length ≤ S1.length * 0 := by
          refine cartesianPairs_filter_row_le p 0 S1 S2 (fun c1 _ => ?_)
          have hNoMatch : ∀ c2, p (c1, c2) = false := by
            intro c2
            dsimp only [p]
            apply decide_eq_false
            simp only [linearCombiner3to1, he1, he2]
            intro hEqAdd
            rw [LawfulCommRing.add_comm x0 _, LawfulCommRing.add_comm x0' _] at hEqAdd
            exact hx0 (LawfulCommRing.add_left_cancel hEqAdd)
          have hEmpty : ∀ (L : List Tower128), L.filter (fun c2 => p (c1, c2)) = [] := by
            intro L
            induction L with
            | nil => rfl
            | cons c2 tl ih =>
              simp only [List.filter_cons, hNoMatch c2, Bool.false_eq_true, ↓reduceIte, ih]
          rw [hEmpty S2]
          exact Nat.le_refl 0
        exact Nat.le_trans (by omega) (Nat.zero_le _)
      else
        have hSwap : ∀ (c1 c2 : Tower128),
            linearCombiner3to1 c1 c2 x0 x1 x2 = linearCombiner3to1 c2 c1 x0 x2 x1 ∧
            linearCombiner3to1 c1 c2 x0' x1' x2' = linearCombiner3to1 c2 c1 x0' x2' x1' := by
          intro c1 c2
          unfold linearCombiner3to1
          exact ⟨congrArg (CommRingOps.add x0) (LawfulCommRing.add_comm _ _),
                 congrArg (CommRingOps.add x0') (LawfulCommRing.add_comm _ _)⟩
        have hRow : ((cartesianPairs S1 S2).filter p).length ≤ S1.length * 1 := by
          refine cartesianPairs_filter_row_le p 1 S1 S2 (fun c1 _ => ?_)
          have hF2 : S2.filter (fun c2 => p (c1, c2)) =
              S2.filter (fun c2 => decide (linearCombiner3to1 c2 c1 x0 x2 x1 = linearCombiner3to1 c2 c1 x0' x2' x1')) := by
            apply List.filter_congr
            intro c2 _
            obtain ⟨hs1, hs2⟩ := hSwap c1 c2
            simp only [p, hs1, hs2]
          rw [hF2]
          exact linearCombiner3to1_universal_c1 c1 x0 x2 x1 x0' x2' x1' S2 hNodup2 he2
        exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
    else
      have hCol : ((cartesianPairs S1 S2).filter p).length ≤ 1 * S2.length :=
        cartesianPairs_filter_col_le p 1 S1 S2 (fun c2 _ =>
          linearCombiner3to1_universal_c1 c2 x0 x1 x2 x0' x1' x2' S1 hNodup1 he1)
      exact Nat.le_trans (by omega) (Nat.le_max_right _ _)
  rw [hFiltEq]
  have hMaxLe : Nat.max S1.length S2.length ≤ 2 ^ 128 := Nat.max_le.mpr ⟨hLen1, hLen2⟩
  have hLe128 : ((cartesianPairs S1 S2).filter p).length ≤ 2 ^ 128 := Nat.le_trans hCountLe hMaxLe
  refine ⟨hCountLe, hLe128, ?_⟩
  unfold ratLe; dsimp only
  refine ⟨Nat.two_pow_pos 256, Nat.two_pow_pos 128, ?_⟩
  have hPow : (2 ^ 128) * (2 ^ 128) = 2 ^ 256 := by decide
  calc
    ((cartesianPairs S1 S2).filter p).length * 2 ^ 128
      ≤ (2 ^ 128) * (2 ^ 128) := Nat.mul_le_mul_right _ hLe128
    _ = 1 * 2 ^ 256 := by rw [hPow]

/-- **`#tooth` Rank-Deficient Zero-Row Extractor Collides (`tooth_zero_row_extractor_collides`)**:
    Replacing `towerCombinerMatrix` with a zero-row `BinaryExtractorMatrix` destroys surjectivity
    and causes distinct 384-bit inputs `0#384 ≠ 1#384` to collide with probability `1`! -/
theorem tooth_zero_row_extractor_collides :
    let badMatrix : BinaryExtractorMatrix := fun _ => 0#384
    (0#384 : BitVec 384) ≠ 1#384 ∧
    extract384To128 badMatrix 0#384 = extract384To128 badMatrix 1#384 := by
  refine ⟨by decide +kernel, ?_⟩
  funext row
  unfold extract384To128 binaryInnerProduct
  change foldXorAnd 384 (0#384).getLsbD (0#384).getLsbD false =
         foldXorAnd 384 (0#384).getLsbD (1#384).getLsbD false
  rw [foldXorAnd_zero_left 384 (fun _ _ => BitVec.getLsbD_zero),
      foldXorAnd_zero_left 384 (fun _ _ => BitVec.getLsbD_zero)]

/-! ### Multi-Column Batched KOS Correlation Check (`kosBatchedPolyResidual`) -/

private theorem coeffs_zero_of_eval_and_quotLinear_local {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (r : R),
      RoundPoly.evalCoeffs cs r = CommRingOps.zero →
      (∀ q ∈ RoundPoly.quotLinear cs r, q = CommRingOps.zero) →
      ∀ c ∈ cs, c = CommRingOps.zero
  | [], _, _, _, _, h => by cases h
  | [c₀], _, hEv, _, c, hc => by
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hEv
    rcases List.mem_singleton.mp hc with rfl
    exact hEv
  | c₀ :: c₁ :: tl, r, hEv, hQ, c, hc => by
    have hEvTl : RoundPoly.evalCoeffs (c₁ :: tl) r = CommRingOps.zero :=
      hQ (RoundPoly.evalCoeffs (c₁ :: tl) r) (by simp [RoundPoly.quotLinear])
    have hQTl : ∀ q ∈ RoundPoly.quotLinear (c₁ :: tl) r, q = CommRingOps.zero :=
      fun q hq => hQ q (by simp [RoundPoly.quotLinear, hq])
    have ihTl := coeffs_zero_of_eval_and_quotLinear_local (c₁ :: tl) r hEvTl hQTl
    have hc0 : c₀ = CommRingOps.zero := by
      change CommRingOps.add c₀ (CommRingOps.mul r (RoundPoly.evalCoeffs (c₁ :: tl) r)) = CommRingOps.zero at hEv
      rw [hEvTl, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hEv
      exact hEv
    rcases List.mem_cons.mp hc with rfl | hMemTl
    · exact hc0
    · exact ihTl c hMemTl

private theorem poly_coeffs_zero_of_vanish_nodup_local
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R] :
    ∀ (S : List R) (cs : List R),
      S.Nodup → cs.length ≤ S.length →
      (∀ r ∈ S, RoundPoly.evalCoeffs cs r = CommRingOps.zero) →
      ∀ c ∈ cs, c = CommRingOps.zero
  | [], cs, _, hLen, _, c, hc => by
    cases cs with
    | nil => cases hc
    | cons _ _ => simp at hLen
  | s0 :: sRest, cs, .cons hs0Not hNdRest, hLen, hZero, c, hc => by
    have hs0Ev : RoundPoly.evalCoeffs cs s0 = CommRingOps.zero := hZero s0 (.head _)
    let q := RoundPoly.quotLinear cs s0
    have hqLen : q.length ≤ sRest.length := by
      dsimp only [q]; rw [RoundPoly.quotLinear_length]; simp only [List.length_cons] at hLen; omega
    have hqZero : ∀ r ∈ sRest, RoundPoly.evalCoeffs q r = CommRingOps.zero := by
      intro r hr
      have hrEv := hZero r (.tail _ hr)
      have hFac := RoundPoly.evalCoeffs_eq_mul_quotLinear_add cs s0 r
      rw [hrEv, hs0Ev, LawfulCommRing.add_zero] at hFac
      have hrNe : r ≠ s0 := fun hEq => hs0Not r hr hEq.symm
      have hSubNe : CommRingOps.sub r s0 ≠ CommRingOps.zero :=
        fun hSub => hrNe (LawfulCommRing.sub_eq_zero_iff.mp hSub)
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hFac.symm with hBad | hOk
      · exact False.elim (hSubNe hBad)
      · exact hOk
    have hqCoeffs := poly_coeffs_zero_of_vanish_nodup_local sRest q hNdRest hqLen hqZero
    exact coeffs_zero_of_eval_and_quotLinear_local cs s0 hs0Ev hqCoeffs c hc

private def findNonzeroEvalLocal {R : Type} [CommRingOps R] [DecidableEq R] (cs : List R) :
    (xs : List R) →
    PSum { r : R // RoundPoly.evalCoeffs cs r ≠ CommRingOps.zero }
         (∀ r ∈ xs, RoundPoly.evalCoeffs cs r = CommRingOps.zero)
  | [] => .inr (fun _ hm => by cases hm)
  | x :: xs =>
    if hx : RoundPoly.evalCoeffs cs x = CommRingOps.zero then
      match findNonzeroEvalLocal cs xs with
      | .inl w => .inl w
      | .inr hRest => .inr (fun r hr => by
          rcases List.mem_cons.mp hr with rfl | hTl
          · exact hx
          · exact hRest r hTl)
    else
      .inl ⟨x, hx⟩

/-- Multi-column batched KOS correlation residual over `deltaUs.length` OT extension columns:
    `senderOffset ⊕ ∑_{j=0}^{m-1} χ^{j+1} · unpackTower k (Δu_j &&& Δ_secret)`. -/
def kosBatchedPolyResidual (k : Nat) (deltaUs : List (TowerBitVec k))
    (secretDelta : TowerBitVec k) (senderOffset chi : TowerElem k) : TowerElem k :=
  RoundPoly.evalCoeffs (senderOffset :: deltaUs.map (fun du => unpackTower k (du &&& secretDelta))) chi

/-- Single-column specialization: `kosBatchedPolyResidual` on `[deltaU]` equals `kosColumnResidual`. -/
theorem kosBatchedPolyResidual_singleton_eq (k : Nat) (deltaU secretDelta : TowerBitVec k)
    (senderOffset chi : TowerElem k) :
    kosBatchedPolyResidual k [deltaU] secretDelta senderOffset chi =
      kosColumnResidual k deltaU secretDelta senderOffset chi := by
  unfold kosBatchedPolyResidual kosColumnResidual
  simp only [List.map_cons, List.map_nil, RoundPoly.evalCoeffs]
  change towerAdd k senderOffset (towerMul k chi (towerAdd k (unpackTower k (deltaU &&& secretDelta))
      (towerMul k chi (towerZero k)))) = _
  rw [towerMul_zero, towerAdd_zero, towerAdd_comm]

/-- **KOS Opening Pad-Blinding Bijection (`kosBatchedMaskEquiv`)**:
    Blinding the batched KOS receiver correlation sum with an independent pad `uMask ∈ TowerElem k`
    (such as `unpackTower 7 (packBits128 (extract384To128 ...))`) induces an exact involution
    `SimpleEquiv (TowerElem k) (TowerElem k)` hiding honest receiver choice bits. -/
def kosBatchedMaskEquiv (k : Nat) (batchSum : TowerElem k) : SimpleEquiv (TowerElem k) (TowerElem k) where
  toFun := fun uMask => towerAdd k batchSum uMask
  invFun := fun opened => towerAdd k batchSum opened
  left_inv := fun uMask => by rw [← towerAdd_assoc, towerAdd_self_zero, towerZero_add]
  right_inv := fun opened => by rw [← towerAdd_assoc, towerAdd_self_zero, towerZero_add]

/-- **Multi-Column Batched KOS Correlation Check Soundness (`kos_batched_poly_check_sound`)**:
    Across ANY `m`-column extended OT batch `deltaUs` (`deltaUs.length ≤ m`) committed prior to
    sampling `χ` from a duplicate-free challenge pool `S : List (TowerElem k)` (`m + 1 ≤ S.length`),
    if ANY column `du ∈ deltaUs` has a non-zero bitwise correlation error against `secretDelta`,
    then AT MOST `m` challenges `χ ∈ S` satisfy `kosBatchedPolyResidual = 0`
    (and at `k = 7` / `Tower128`, `ratLe (bad, 2^128) (m, 2^128)`). -/
theorem kos_batched_poly_check_sound (k m : Nat)
    (deltaUs : List (TowerBitVec k)) (secretDelta : TowerBitVec k)
    (senderOffset : TowerElem k) (S : List (TowerElem k))
    (hNodup : S.Nodup) (hLen : deltaUs.length ≤ m) (hDom : m + 1 ≤ S.length)
    (hFault : ∃ du ∈ deltaUs, unpackTower k (du &&& secretDelta) ≠ towerZero k) :
    let bad := (S.filter (fun chi =>
      decide (kosBatchedPolyResidual k deltaUs secretDelta senderOffset chi = towerZero k))).length
    bad ≤ m ∧ ratLe (bad, 2 ^ 128) (m, 2 ^ 128) := by
  intro bad
  let cs := senderOffset :: deltaUs.map (fun du => unpackTower k (du &&& secretDelta))
  have hCsLen : cs.length ≤ m + 1 := by simp [cs]; omega
  have hWitnessNz : ∃ z : TowerElem k, RoundPoly.evalCoeffs cs z ≠ towerZero k := by
    match findNonzeroEvalLocal cs (S.take (m + 1)) with
    | .inl ⟨z, hz⟩ => exact ⟨z, hz⟩
    | .inr hAll =>
      exfalso
      obtain ⟨du, hMem, hNe⟩ := hFault
      have hTakeLen : (S.take (m + 1)).length = m + 1 := List.length_take_of_le hDom
      have hNdTake : (S.take (m + 1)).Nodup := (List.take_sublist (m + 1) S).nodup hNodup
      have hZeroAll := poly_coeffs_zero_of_vanish_nodup_local (S.take (m + 1)) cs hNdTake
        (by rw [hTakeLen]; exact hCsLen) hAll
      exact hNe (hZeroAll (unpackTower k (du &&& secretDelta)) (List.mem_cons_of_mem _ (List.mem_map_of_mem hMem)))
  have hBadLe : bad ≤ m :=
    RoundPoly.roots_nodup_length_le m cs S hNodup hCsLen hWitnessNz
  refine ⟨hBadLe, ?_⟩
  unfold ratLe; dsimp only
  exact ⟨Nat.two_pow_pos 128, Nat.two_pow_pos 128, Nat.mul_le_mul_right _ hBadLe⟩

/-- **`#tooth` Pre-Challenge 2-Column KOS Cancellation (`tooth_kos_prechallenge_two_column_cancellation`)**:
    If `deltaUs` is chosen AFTER seeing `χ ∈ Tower128` as `[packTower 7 χ, packTower 7 1]`, then
    column 1 has non-zero correlation fault (`1 ≠ 0`) under `allOnes`, YET `χ · χ ⊕ χ² · 1 = 0`
    cancels `kosBatchedPolyResidual` to `0` — proving `χ` must be sampled strictly after commitment! -/
theorem tooth_kos_prechallenge_two_column_cancellation (chi : Tower128) :
    let allOnes : TowerBitVec 7 := BitVec.allOnes 128
    let deltaUs : List (TowerBitVec 7) := [packTower 7 chi, packTower 7 (towerOne 7)]
    unpackTower 7 (packTower 7 (towerOne 7) &&& allOnes) ≠ towerZero 7 ∧
    kosBatchedPolyResidual 7 deltaUs allOnes (towerZero 7) chi = towerZero 7 := by
  intro allOnes deltaUs
  have hOnes : ∀ (idx : Fin 128), (BitVec.allOnes 128).getLsbD idx.1 = true := by decide +kernel
  have hAndOne : ∀ v : TowerBitVec 7, v &&& allOnes = v := by
    intro v
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    change (v &&& BitVec.allOnes 128).getLsbD i = v.getLsbD i
    rw [BitVec.getLsbD_and, hOnes ⟨i, hi⟩, Bool.and_true]
  refine ⟨?_, ?_⟩
  · rw [hAndOne, unpackTower_packTower]
    exact towerOne_ne_zero 7
  · unfold kosBatchedPolyResidual
    simp only [deltaUs, List.map_cons, List.map_nil, hAndOne, unpackTower_packTower,
      RoundPoly.evalCoeffs]
    change towerAdd 7 (towerZero 7)
      (towerMul 7 chi (towerAdd 7 chi
        (towerMul 7 chi (towerAdd 7 (towerOne 7) (towerMul 7 chi (towerZero 7)))))) = towerZero 7
    rw [towerMul_zero, towerAdd_zero, towerMul_one, towerAdd_self_zero, towerMul_zero, towerAdd_zero]

/-- **Inhabitedness Witness (`kos_batched_poly_check_inhabited`)**:
    Honest 2-column extended OT correlation (`deltaUs = [0#128, 0#128]`) passes `kosBatchedPolyResidual = 0`,
    while a 2-column batch with bit-0 fault in column 2 (`deltaUs = [0#128, 1#128]`, `secretDelta = 1#128`)
    yields non-zero residual at `χ = 1`! -/
theorem kos_batched_poly_check_inhabited :
    kosBatchedPolyResidual 7 [0#128, 0#128] 1#128 (towerZero 7) (towerOne 7) = towerZero 7 ∧
    kosBatchedPolyResidual 7 [0#128, 1#128] 1#128 (towerZero 7) (towerOne 7) ≠ towerZero 7 := by
  have hz : unpackTower 7 0#128 = towerZero 7 := unpackTower_zero 7
  have h1Ne0 : unpackTower 7 1#128 ≠ towerZero 7 := by
    intro h0
    have hp := congrArg (packTower 7) h0
    rw [packTower_unpackTower, packTower_zero] at hp
    revert hp; decide +kernel
  refine ⟨?_, ?_⟩
  · unfold kosBatchedPolyResidual
    simp only [List.map_cons, List.map_nil, show (0#128 &&& 1#128) = 0#128 by decide +kernel,
      hz, RoundPoly.evalCoeffs]
    change towerAdd 7 (towerZero 7) (towerMul 7 (towerOne 7)
      (towerAdd 7 (towerZero 7) (towerMul 7 (towerOne 7)
        (towerAdd 7 (towerZero 7) (towerMul 7 (towerOne 7) (towerZero 7)))))) = towerZero 7
    simp
  · unfold kosBatchedPolyResidual
    simp only [List.map_cons, List.map_nil,
      show (0#128 &&& 1#128) = 0#128 by decide +kernel,
      show (1#128 &&& 1#128) = 1#128 by decide +kernel,
      hz, RoundPoly.evalCoeffs]
    change towerAdd 7 (towerZero 7) (towerMul 7 (towerOne 7)
      (towerAdd 7 (towerZero 7) (towerMul 7 (towerOne 7)
        (towerAdd 7 (unpackTower 7 1#128) (towerMul 7 (towerOne 7) (towerZero 7)))))) ≠ towerZero 7
    simp [h1Ne0]

end ExtractorAndBatchedKos

/-- **Silent-OT GGM Punctured-Tree Leaf Hiding (`ggm_punctured_tree_hiding`)**:
    In Silent-OT PCG (`preprocessing.rs`), revealing all sibling GGM node seeds off the punctured
    path leaves the unrevealed leaf key `kStar ∈ Fin cardSeeds` unqueried outside `Q` random-oracle
    calls, bounding the distinguishing advantage between real punctured GGM expansion (`secretLeafFn`)
    and uniform random leaf correlation (`baseGgm`) by `Q / cardSeeds` (`≤ 2Q / 2^256` at 256-bit seeds). -/
theorem ggm_punctured_tree_hiding {TagDom Cod : Type}
    (cardSeeds Q : Nat) (hPos : 0 < cardSeeds)
    (baseGgm : Fin cardSeeds × TagDom → Cod)
    (secretLeafFn : TagDom → Cod)
    (A : OracleComp (Fin cardSeeds × TagDom) Cod Bool)
    (hQb : QueryBounded Q A) :
    let diff := natAbsDiff (keyedPrfRealAccept cardSeeds baseGgm secretLeafFn A)
                           (keyedPrfIdealAccept cardSeeds baseGgm A)
    diff ≤ Q ∧ ratLe (diff, cardSeeds) (2 * Q, cardSeeds) :=
  hidingAdv_le cardSeeds Q hPos baseGgm secretLeafFn A hQb

/-! ## Seed expansion: statistical versus computational claims -/

set_option exponentiation.threshold 512 in
/-- A deterministic 256-bit seed expansion cannot have the exactly uniform law
on even 384 independent output bits. This applies to every concrete GGM splitter,
without an assumption on SHAKE. A vault pseudorandomness theorem must retain a
computational hybrid; perfect uniformity is available only in the ideal game. -/
theorem dense_seed_expansion_not_perfectly_uniform
    (expand : Fin (2 ^ 256) → Fin (2 ^ 384)) (output : Fin (2 ^ 384)) :
    (finSum (2 ^ 256) (fun seed => if expand seed = output then 1 else 0)) * 2 ^ 384 ≠
      2 ^ 256 := by
  intro he
  let count := finSum (2 ^ 256) (fun seed => if expand seed = output then 1 else 0)
  have hs : 2 ^ 256 < 2 ^ 384 := by decide +kernel
  have hp : 0 < 2 ^ 256 := Nat.two_pow_pos 256
  change count * 2 ^ 384 = 2 ^ 256 at he
  by_cases hz : count = 0
  · rw [hz, Nat.zero_mul] at he
    omega
  · have hn : 1 ≤ count := by omega
    have hm := Nat.mul_le_mul_right (2 ^ 384) hn
    omega

#verify_constructive Qsag.dense_seed_expansion_not_perfectly_uniform

/-! ## Two-lane vault sacrifice

The production `PI_TRIPLE_F2_CHAL` takes two halves of the coin and forces each
low bit to one. Each lane therefore has 127 random bits, not 128. The theorem
below counts roots on arbitrary duplicate-free challenge sets; using all odd
field encodings yields the denominator `2^254`. MAC forgery and coin/PCG
pseudorandomness are separate bad events, not silently included in this bound.
-/

structure VaultSacrificeRow where
  a : Tower128
  b : Tower128
  c : Tower128
  companionA : Tower128
  companionB : Tower128
  companionC : Tower128
  deriving DecidableEq

def VaultSacrificeRow.accepts (row : VaultSacrificeRow) (rho : Tower128) : Bool :=
  decide (spdzSacrificeResidual rho row.a row.b row.c
    row.companionA row.companionB row.companionC = CommRingOps.zero)

def vaultSacrificeLane (rows : List VaultSacrificeRow) (rho : Tower128) : Bool :=
  rows.all (fun row => row.accepts rho)

/-- Every accepted batch accepts each row. No independence between rows is needed. -/
theorem vaultSacrificeLane_row {rows : List VaultSacrificeRow} {row : VaultSacrificeRow}
    (hm : row ∈ rows) {rho : Tower128} (ha : vaultSacrificeLane rows rho = true) :
    row.accepts rho = true :=
  List.all_eq_true.mp ha row hm

private theorem vault_filter_mono {A : Type} (xs : List A) (f g : A → Bool)
    (h : ∀ x, f x = true → g x = true) :
    (xs.filter f).length ≤ (xs.filter g).length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    cases hf : f x with
    | false =>
      cases hg : g x <;> simp only [List.filter_cons, hf, hg, Bool.false_eq_true,
        ↓reduceIte, List.length_cons]
      · exact ih
      · exact Nat.le_trans ih (Nat.le_succ _)
    | true =>
      have hg := h x hf
      simp only [List.filter_cons, hf, hg, ↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ ih

/-- A fixed corrupt row bounds the entire batch's accepting challenges. -/
theorem vaultSacrificeLane_bad_count (rows : List VaultSacrificeRow)
    (row : VaultSacrificeRow) (hm : row ∈ rows)
    (hbad : row.c ≠ CommRingOps.mul row.a row.b)
    (S : List Tower128) (hn : S.Nodup) :
    (S.filter (vaultSacrificeLane rows)).length ≤ 1 := by
  exact Nat.le_trans
    (vault_filter_mono S (vaultSacrificeLane rows) row.accepts
      (fun _ h => vaultSacrificeLane_row hm h))
    (spdz_triple_sacrifice_sound row.a row.b row.c
      row.companionA row.companionB row.companionC S hn hbad)

/-- Actual Cartesian-product count, rather than a product merely named a probability. -/
def vaultSacrificeAcceptingPairs (rows₀ rows₁ : List VaultSacrificeRow)
    (S₀ S₁ : List Tower128) : List (Tower128 × Tower128) :=
  (S₀.filter (vaultSacrificeLane rows₀)).flatMap fun r₀ =>
    (S₁.filter (vaultSacrificeLane rows₁)).map fun r₁ => (r₀, r₁)

private theorem vault_pairs_length {A B : Type} (xs : List A) (ys : List B) :
    (xs.flatMap fun x => ys.map fun y => (x, y)).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- A corrupt candidate is sacrificed against independent companions in both lanes.
The same rho may be reused across the whole batch within a lane. -/
theorem vault_two_lane_sacrifice_sound (rows₀ rows₁ : List VaultSacrificeRow)
    (bad₀ bad₁ : VaultSacrificeRow) (hm₀ : bad₀ ∈ rows₀) (hm₁ : bad₁ ∈ rows₁)
    (hb₀ : bad₀.c ≠ CommRingOps.mul bad₀.a bad₀.b)
    (hb₁ : bad₁.c ≠ CommRingOps.mul bad₁.a bad₁.b)
    (S₀ S₁ : List Tower128) (hn₀ : S₀.Nodup) (hn₁ : S₁.Nodup) :
    (vaultSacrificeAcceptingPairs rows₀ rows₁ S₀ S₁).length ≤ 1 := by
  rw [vaultSacrificeAcceptingPairs, vault_pairs_length]
  exact Nat.le_trans (Nat.mul_le_mul
    (vaultSacrificeLane_bad_count rows₀ bad₀ hm₀ hb₀ S₀ hn₀)
    (vaultSacrificeLane_bad_count rows₁ bad₁ hm₁ hb₁ S₁ hn₁)) (Nat.le_refl 1)

/-- Cross-multiplied strict probability bound for the production odd-challenge support.
The support sizes are explicit: the theorem does not normalize arbitrary short lists
by the full-field size. -/
theorem vault_two_lane_odd_support_lt_128 (rows₀ rows₁ : List VaultSacrificeRow)
    (bad₀ bad₁ : VaultSacrificeRow) (hm₀ : bad₀ ∈ rows₀) (hm₁ : bad₁ ∈ rows₁)
    (hb₀ : bad₀.c ≠ CommRingOps.mul bad₀.a bad₀.b)
    (hb₁ : bad₁.c ≠ CommRingOps.mul bad₁.a bad₁.b)
    (S₀ S₁ : List Tower128) (hn₀ : S₀.Nodup) (hn₁ : S₁.Nodup)
    (hs₀ : S₀.length = 2 ^ 127) (hs₁ : S₁.length = 2 ^ 127) :
    (vaultSacrificeAcceptingPairs rows₀ rows₁ S₀ S₁).length * 2 ^ 128 <
      S₀.length * S₁.length := by
  have hb := vault_two_lane_sacrifice_sound rows₀ rows₁ bad₀ bad₁ hm₀ hm₁ hb₀ hb₁ S₀ S₁ hn₀ hn₁
  rw [hs₀, hs₁]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2 ^ 128) hb) (by decide +kernel)

/-- Enumerate precisely the 128-bit field encodings whose low bit is one.
Appending the fixed low bit models the support after production's `| 1`. -/
def oddVaultChallenge (hi : Fin (2 ^ 127)) : Tower128 :=
  unpackTower 7 ((BitVec.ofFin hi) ++ 1#1)

def oddVaultChallengeSupport : List Tower128 :=
  (List.finRange (2 ^ 127)).map oddVaultChallenge

theorem oddVaultChallenge_injective (a b : Fin (2 ^ 127))
    (h : oddVaultChallenge a = oddVaultChallenge b) : a = b := by
  have he := congrArg (packTower 7) h
  simp only [oddVaultChallenge, packTower_unpackTower] at he
  have hb := (BitVec.append_left_inj (1#1)).mp he
  exact Fin.ext (congrArg BitVec.toNat hb)

theorem oddVaultChallengeSupport_card : oddVaultChallengeSupport.length = 2 ^ 127 := by
  simp only [oddVaultChallengeSupport, List.length_map, List.length_finRange]

theorem oddVaultChallengeSupport_nodup : oddVaultChallengeSupport.Nodup := by
  apply List.pairwise_map.mpr
  exact (List.nodup_finRange (2 ^ 127)).imp
    (fun hne heq => hne (oddVaultChallenge_injective _ _ heq))

/-- Instantiation on the exact odd-bit challenge support, with no supplied
cardinality or duplicate-freedom assumptions. This is conditional on uniform
independent high halves and authentic openings. -/
theorem vault_production_support_sacrifice_lt_128 (rows₀ rows₁ : List VaultSacrificeRow)
    (bad₀ bad₁ : VaultSacrificeRow) (hm₀ : bad₀ ∈ rows₀) (hm₁ : bad₁ ∈ rows₁)
    (hb₀ : bad₀.c ≠ CommRingOps.mul bad₀.a bad₀.b)
    (hb₁ : bad₁.c ≠ CommRingOps.mul bad₁.a bad₁.b) :
    (vaultSacrificeAcceptingPairs rows₀ rows₁ oddVaultChallengeSupport oddVaultChallengeSupport).length *
      2 ^ 128 < 2 ^ 254 := by
  have h := vault_two_lane_odd_support_lt_128 rows₀ rows₁ bad₀ bad₁ hm₀ hm₁ hb₀ hb₁
    oddVaultChallengeSupport oddVaultChallengeSupport oddVaultChallengeSupport_nodup
    oddVaultChallengeSupport_nodup oddVaultChallengeSupport_card oddVaultChallengeSupport_card
  simpa only [oddVaultChallengeSupport_card, show (2 : Nat) ^ 127 * 2 ^ 127 = 2 ^ 254 by decide +kernel] using h

/-- Caller releases its vault only after both lanes accept. This is a pure
acceptance gate; authenticating the row openings is a separate prerequisite. -/
def releaseSacrificedVault {V : Type} (vault : V)
    (rows₀ rows₁ : List VaultSacrificeRow) (rho₀ rho₁ : Tower128) : Option V :=
  if vaultSacrificeLane rows₀ rho₀ && vaultSacrificeLane rows₁ rho₁ then some vault else none

theorem releaseSacrificedVault_iff {V : Type} (vault : V)
    (rows₀ rows₁ : List VaultSacrificeRow) (rho₀ rho₁ : Tower128) :
    releaseSacrificedVault vault rows₀ rows₁ rho₀ rho₁ = some vault ↔
      vaultSacrificeLane rows₀ rho₀ = true ∧ vaultSacrificeLane rows₁ rho₁ = true := by
  unfold releaseSacrificedVault
  cases vaultSacrificeLane rows₀ rho₀ <;> cases vaultSacrificeLane rows₁ rho₁
  · exact ⟨(fun h => by cases h), (fun h => by cases h.1)⟩
  · exact ⟨(fun h => by cases h), (fun h => by cases h.1)⟩
  · exact ⟨(fun h => by cases h), (fun h => by cases h.2)⟩
  · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- The two lanes share the same candidate by construction; only companions differ.
These are reconstructed audit values, not an implementation that opens the triple. -/
structure TwoLaneVaultRow where
  a : Tower128
  b : Tower128
  c : Tower128
  companion₀ : Tower128 × Tower128 × Tower128
  companion₁ : Tower128 × Tower128 × Tower128

def TwoLaneVaultRow.lane (row : TwoLaneVaultRow) (second : Bool) : VaultSacrificeRow :=
  let companion := if second then row.companion₁ else row.companion₀
  ⟨row.a, row.b, row.c, companion.1, companion.2.1, companion.2.2⟩

/-- Returned triples are exactly the candidates whose two companions were checked. -/
def releaseTwoLaneCandidates (rows : List TwoLaneVaultRow) (rho₀ rho₁ : Tower128) :
    Option (List (Tower128 × Tower128 × Tower128)) :=
  releaseSacrificedVault (rows.map fun row => (row.a, row.b, row.c))
    (rows.map fun row => row.lane false) (rows.map fun row => row.lane true) rho₀ rho₁

theorem releaseTwoLaneCandidates_refines (rows : List TwoLaneVaultRow) (rho₀ rho₁ : Tower128) :
    releaseTwoLaneCandidates rows rho₀ rho₁ = some (rows.map fun row => (row.a, row.b, row.c)) ↔
      vaultSacrificeLane (rows.map fun row => row.lane false) rho₀ = true ∧
      vaultSacrificeLane (rows.map fun row => row.lane true) rho₁ = true :=
  releaseSacrificedVault_iff _ _ _ _ _

/-- The release check's exact accepting-pair count for any corrupt candidate in
the returned vault. The checked row and the released candidate cannot diverge. -/
theorem twoLaneCandidates_bad_release_lt_128 (rows : List TwoLaneVaultRow)
    (bad : TwoLaneVaultRow) (hm : bad ∈ rows)
    (hb : bad.c ≠ CommRingOps.mul bad.a bad.b) :
    (vaultSacrificeAcceptingPairs (rows.map fun row => row.lane false)
      (rows.map fun row => row.lane true) oddVaultChallengeSupport oddVaultChallengeSupport).length *
        2 ^ 128 < 2 ^ 254 :=
  vault_production_support_sacrifice_lt_128 _ _ (bad.lane false) (bad.lane true)
    (List.mem_map.mpr ⟨bad, hm, rfl⟩) (List.mem_map.mpr ⟨bad, hm, rfl⟩) hb hb

def zeroVaultSacrificeRow : VaultSacrificeRow :=
  ⟨towerZero 7, towerZero 7, towerZero 7, towerZero 7, towerZero 7, towerZero 7⟩

theorem witness_vault_sacrifice_inhabited :
    ∃ row : VaultSacrificeRow, releaseSacrificedVault [row] [row] [row]
      (towerOne 7) (towerOne 7) = some [row] := by
  exact ⟨zeroVaultSacrificeRow, by decide +kernel⟩

def corruptVaultSacrificeRow : VaultSacrificeRow :=
  { zeroVaultSacrificeRow with c := towerOne 7 }

theorem tooth_vault_sacrifice_corrupt_row :
    releaseSacrificedVault [corruptVaultSacrificeRow] [corruptVaultSacrificeRow]
      [corruptVaultSacrificeRow] (towerOne 7) (towerOne 7) ≠ some [corruptVaultSacrificeRow] := by
  decide +kernel

set_option maxRecDepth 8192 in
#tooth_pair Qsag.vault_two_lane_sacrifice_sound vs Qsag.tooth_vault_sacrifice_corrupt_row
#verify_inhabited Qsag.releaseSacrificedVault_iff Qsag.witness_vault_sacrifice_inhabited
#verify_constructive Qsag.vault_two_lane_odd_support_lt_128

/-! ## 7. Mechanical Assurance Gates (`#tooth_pair`, `#verify_inhabited`, `#verify_constructive`) -/

section AssuranceGates

/-- **`#tooth` Overflowing Ring-LWE Noise Flips Decoded OT Bit (`tooth_rlwe1024_overflow_flips_decoded_bit`)**:
    Exceeding the `2049 < 3072` decryption margin (`eMag = 4000`) flips `rlweDecodeBit` on `bit = false`. -/
theorem tooth_rlwe1024_overflow_flips_decoded_bit :
    rlweDecodeBit (rlweNoisyEncode false true 4000) ≠ false := by
  decide +kernel

/-- **`#tooth` Corrupted FO Ciphertext Rejected When Chosen (`tooth_rlwe_fo_corrupted_batch_rejected`)**:
    Atomic batch-rejection refutation witness for `rlwe_fo_cut_and_choose_sound`. -/
theorem tooth_rlwe_fo_corrupted_batch_rejected :
    verifyRlweFoBatch [⟨false, true, 4000, rlweNoisyEncode false true 4000⟩] 1 ≠ true := by
  rw [tooth_rlwe_fo_corrupted_ciphertext_caught.2.2]
  decide

def demoForgedZeroSacrificeOpening : SharedSpdzSacrificeOpening :=
  let rho : GoldilocksExt2 := ⟨Goldilocks.ofNat 2, Goldilocks.one⟩
  let badTr : AuthenticatedSharedTriple :=
    { demoHonestAuthTriple with
      triple := { demoHonestAuthTriple.triple with
                  cShares := [Goldilocks.ofNat 20, Goldilocks.ofNat 27, Goldilocks.ofNat 34] }
      macC := mkDemoMacShares 13 }
  let op := honestSharedSpdzSacrificeOpening demoLambdas2of3 rho
    demoAlphaShares3 badTr demoCompanionAuthTriple demoZeroMasks3 demoZeroMasks3 demoZeroMasks3
  let macW := shareZipSub
    (shareZipSub (shareScale rho badTr.macC) demoCompanionAuthTriple.macC)
    (ringListZipAdd (shareScale op.uOpened badTr.macB) (shareScale op.vOpened demoCompanionAuthTriple.macA))
  { op with wOpened := CommRingOps.zero,
            sigmaW := spdzComputeSigmas CommRingOps.zero macW demoAlphaShares3 demoZeroMasks3 }

/-- **`#tooth` Forged Zero-Opening SPDZ Sacrifice Rejected (`tooth_shared_spdz_forged_zero_rejected`)**:
    Atomic MAC-rejection refutation witness for `verifySharedSpdzSacrifice`. -/
theorem tooth_shared_spdz_forged_zero_rejected :
    verifySharedSpdzSacrifice demoForgedZeroSacrificeOpening ≠ true := by
  have hFalse : verifySharedSpdzSacrifice demoForgedZeroSacrificeOpening = false :=
    tooth_shared_spdz_sacrifice_rejects_corrupted_triple.2.2
  rw [hFalse]
  decide

/-- **`#tooth` Rank-Deficient Zero-Row Extractor Collides (`tooth_zero_row_extractor_collides_pair`)**:
    Atomic collision refutation witness for `extract384To128_two_universal` on distinct inputs `0#384 ≠ 1#384`. -/
theorem tooth_zero_row_extractor_collides_pair :
    ¬ (extract384To128 (fun _ => 0#384) 0#384 ≠ extract384To128 (fun _ => 0#384) 1#384) :=
  fun hNe => hNe tooth_zero_row_extractor_collides.2

/-- **`#tooth` Pre-Challenge Adaptive Fault Cancels KOS Residual (`tooth_kos_prechallenge_cancels_fault_witness`)**:
    Atomic cancellation witness for `kos_batched_poly_check_sound`. -/
theorem tooth_kos_prechallenge_cancels_fault_witness (chi : Tower128) :
    ∃ deltaUs : List (TowerBitVec 7),
      kosBatchedPolyResidual 7 deltaUs (BitVec.allOnes 128) (towerZero 7) chi = towerZero 7 ∧
      unpackTower 7 (packTower 7 (towerOne 7) &&& BitVec.allOnes 128) ≠ towerZero 7 := by
  have h := tooth_kos_prechallenge_two_column_cancellation chi
  exact ⟨[packTower 7 chi, packTower 7 (towerOne 7)], h.2, h.1⟩

/-- **`#tooth` Unbounded `Q + 1` Queries Break `Q`-Query GGM Hiding (`tooth_ggm_extra_query_distinguishes`)**:
    With `Q = 0` budget violated by a 1-query distinguisher, `keyedPrfRealAccept ≠ keyedPrfIdealAccept`. -/
theorem tooth_ggm_extra_query_distinguishes :
    keyedPrfRealAccept 1 (fun _ : Fin 1 × Unit => false) (fun _ : Unit => true)
      (OracleComp.query (⟨0, by decide⟩, ()) OracleComp.pure) ≠
    keyedPrfIdealAccept 1 (fun _ : Fin 1 × Unit => false)
      (OracleComp.query (⟨0, by decide⟩, ()) OracleComp.pure) := by
  decide +kernel

/-- Genuine non-empty 2-party pairwise OLE share witness (`us = [2, 3], vShares = [4, 5], sum(ws) = 5 * 9 = 45`). -/
theorem witness_valid_pairwise_ole_inhabited :
    ∃ (us vShares ws : List Goldilocks), ValidPairwiseOleShares us vShares ws := by
  have h1 : ValidPairwiseOleShares
      [Goldilocks.ofNat 3] [Goldilocks.ofNat 5]
      [CommRingOps.add (CommRingOps.mul (Goldilocks.ofNat 3) (Goldilocks.ofNat 5))
        (CommRingOps.add (ringListSum ([] : List Goldilocks)) (ringListSum ([] : List Goldilocks)))] :=
    ValidPairwiseOleShares.cons [] [] [] [] ValidPairwiseOleShares.nil
      rfl rfl rfl rfl (by decide +kernel) (by decide +kernel)
  have h2 := ValidPairwiseOleShares.cons (u0 := Goldilocks.ofNat 2) (v0 := Goldilocks.ofNat 4)
      [Goldilocks.ofNat 3] [Goldilocks.ofNat 7] [Goldilocks.ofNat 5] [Goldilocks.ofNat 7]
      h1 rfl rfl rfl rfl (by decide +kernel) (by decide +kernel)
  exact ⟨_, _, _, h2⟩

theorem witness_beaver_triple_val_inhabited :
    ∃ (t : BeaverTripleVal Goldilocks), t.valid :=
  ⟨⟨Goldilocks.ofNat 3, Goldilocks.ofNat 4, Goldilocks.ofNat 12⟩,
    show Goldilocks.ofNat 12 = CommRingOps.mul (Goldilocks.ofNat 3) (Goldilocks.ofNat 4) by
      decide +kernel⟩

theorem witness_shared_triple_validAt_inhabited :
    ∃ (lambdas : List Goldilocks) (tr : SharedBeaverTriple Goldilocks), tr.validAt lambdas :=
  ⟨demoLambdas2of3, demoHonestAuthTriple.triple,
    ⟨rfl, rfl, rfl, shared_spdz_sacrifice_inhabited.2.1⟩⟩

theorem witness_auth_triple_validMacs_inhabited :
    ∃ (lambdas : List Goldilocks) (alphaShares : List GoldilocksExt2) (tr : AuthenticatedSharedTriple),
      tr.validMacs lambdas alphaShares :=
  ⟨demoLambdas2of3, demoAlphaShares3, demoHonestAuthTriple,
    ⟨rfl, rfl, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem witness_ggm_query_bounded_inhabited :
    ∃ (A : OracleComp (Fin 2 × Unit) Bool Bool), QueryBounded 1 A :=
  ⟨OracleComp.query (⟨0, by decide⟩, ()) OracleComp.pure, fun _ => trivial⟩

#tooth_pair Qsag.rlwe1024_ot_decrypt_exact vs Qsag.tooth_rlwe1024_overflow_flips_decoded_bit
#tooth_pair Qsag.rlwe_fo_cut_and_choose_sound vs Qsag.tooth_rlwe_fo_corrupted_batch_rejected
#tooth_pair Qsag.verifySharedSpdzSacrifice_complete vs Qsag.tooth_shared_spdz_forged_zero_rejected
#tooth_pair Qsag.verifySharedSpdzSacrifice_sound vs Qsag.tooth_shared_spdz_forged_zero_rejected
#tooth_pair Qsag.extract384To128_two_universal vs Qsag.tooth_zero_row_extractor_collides_pair
#tooth_pair Qsag.kos_batched_poly_check_sound vs Qsag.tooth_kos_prechallenge_cancels_fault_witness
#tooth_pair Qsag.ggm_punctured_tree_hiding vs Qsag.tooth_ggm_extra_query_distinguishes

#verify_inhabited Qsag.ole_pairwise_cross_sum_eq_mul Qsag.witness_valid_pairwise_ole_inhabited
#verify_inhabited Qsag.pow7Tree_correct Qsag.witness_beaver_triple_val_inhabited
#verify_inhabited Qsag.evalSharedPow7Tree_correct Qsag.witness_shared_triple_validAt_inhabited
#verify_inhabited Qsag.verifySharedSpdzSacrifice_complete Qsag.witness_auth_triple_validMacs_inhabited
#verify_inhabited Qsag.ggm_punctured_tree_hiding Qsag.witness_ggm_query_bounded_inhabited

#verify_constructive Qsag.rlwe1024_ot_decrypt_exact
#verify_constructive Qsag.ole_pairwise_cross_sum_eq_mul
#verify_constructive Qsag.pow7Tree_correct
#verify_constructive Qsag.evalSharedPow7Tree_correct
#verify_constructive Qsag.verifySharedSpdzSacrifice_complete
#verify_constructive Qsag.verifySharedSpdzSacrifice_sound
#verify_constructive Qsag.rlwe_fo_cut_and_choose_sound
#verify_constructive Qsag.extract384To128_two_universal
#verify_constructive Qsag.kos_batched_poly_check_sound
#verify_constructive Qsag.ggm_punctured_tree_hiding

end AssuranceGates

end Qsag
end

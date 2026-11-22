module
/-
# Qsag.Math.Q192BernoulliTailBound — Q192 Bernoulli rejection step of the production Gaussian sampler

Integer model of `gaussian_exp_probability`, `gaussian_fraction_lt` and one trial of
`sample_gaussian_box` in `crates/qsag-core/src/preprocessing.rs`, with:
1. the transcribed table `RLWE_GAUSSIAN_EXP_POWERS` and the masked multiply-and-shift evaluator,
2. the exact acceptance count of the 192-bit threshold comparison over its coin space,
3. the per-exponent error of the evaluator against every factor vector inside the table bracket,
4. total-variation bounds, in cross-multiplied integer form, for one coordinate and for
   finite products of coordinates, with transfer to arbitrary events,
5. an 8-bit truncation witness that violates the same bounds.

There are no real numbers here. An ideal law is a vector of natural-number weights known up to
a common rational scale; every statement quantifies over all such vectors inside a bracket.
-/
public import Qsag.Spec.GameBound
public import Qsag.Math.CyclotomicRlwe
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Table and evaluator -/

/-- `RLWE_GAUSSIAN_EXP_POWERS`: entry `i` is the three little-endian 64-bit limbs of the Rust
    constant read as one natural number (`limb0 + limb1 * 2^64 + limb2 * 2^128`). The Rust
    source documents entry `i` as `floor(2^192 * exp(-2^i / 980000))`. -/
@[expose] def rlweGaussianExpPowers : List Nat :=
  [0xffffeee161ee8ccb4596fdd04820cdf51e0ee5c166ce3f45,
   0xffffddc2c5022e3e4a2b8823ca1b4080c4bd6a5137eea0f8,
   0xffffbb858e98aecd2a9c7998b671a80144427bc76a53ff98,
   0xffff770b2f82a4698111b86300311166a0c9a58e0e64155f,
   0xfffeee16a84a50764c35e0bc42b0f5a835a41e9244e165f3,
   0xfffddc2e75a822aedf95f9d82b4679521d0613f7ebafa37a,
   0xfffbb8617f996614692edb6ffd64b91e1cc31b117b42ceb3,
   0xfff770d550301cb94a27dce9e6d3509929767ac0a297cf82,
   0xffeee1f3e31bedf931988b3d23e474e3adb8566b5ff3f42d,
   0xffddc50cc75a8994f4f6785cfd4602526750e998b9b340e1,
   0xffbb8ead44e33bdceeabfe39f8fd5b4ed196fffa1ed986fd,
   0xff772fa6efe402eddc50d69edfd2a16006cff414fc79dc4f,
   0xfeeea86be7f9fcc24b9e8aa4ca5654b6d0d009324a025ffe,
   0xfdde74b3b7c5345760409dd8686a08e8aaf2184fd58065f9,
   0xfbc173f9d621e030b4ec92392fe9aad0965a565c6d111b08,
   0xf794eb9bfd25b6e83ca73c0a1d21b6eb60aeffc51a982010,
   0xef70b54847b33c5f655e44e2d45921a000bc34df6dfa8348,
   0xdff3a41c157eb15acf047b168746a1be647298b2cc3a9ced,
   0xc3ea5fc9e3f7861fefcffdd9e95adf361e445c07efd41bd3,
   0x95eee480d2374d3f54f67e49ba14782464853bde5727d2ff,
   0x57cff4eba030f604c02dbeaedb0d80fab99bb3368bc0d7af,
   0x1e1f0166264058a1e967d9885d91350977d66aade9197cc5,
   0x038b481547b64d6a6b99ed77f4585a5ed17313b79cc3aba7,
   0x000c8f77db161fe3f3a1a5781f3b6abe36d997f1617c1bac,
   0x0000009dc3a3a8f31f1003bc1c6467028102ba277dc54cf0,
   0x00000000000061398c3ff6371010887929065424ef536df9,
   0x00000000000000000000000024eca93839e763f90442732a,
   0x000000000000000000000000000000000000000000000000,
   0x000000000000000000000000000000000000000000000000,
   0x000000000000000000000000000000000000000000000000]

/-- Table entry `i`, and `0` past the end of the table. -/
@[expose] def gaussianExpPower (i : Nat) : Nat := rlweGaussianExpPowers.getD i 0

/-- Masked multiply-and-shift loop over a table `tbl` at fixed-point modulus `Q`: the state
    starts at `Q - 1`; step `bit` replaces it by `⌊state * tbl bit / Q⌋` when bit `bit` of `e`
    is set and keeps it otherwise. The last argument is the number of steps done. -/
def fixedExpFold (Q : Nat) (tbl : Nat → Nat) (e : Nat) : Nat → Nat
  | 0 => Q - 1
  | bits + 1 =>
    if e.testBit bits then fixedExpFold Q tbl e bits * tbl bits / Q else fixedExpFold Q tbl e bits

/-- `gaussian_exp_probability::<BITS>(exponent)` as a natural number below `2^192`. -/
@[expose] def gaussianExpProbability (bits exponent : Nat) : Nat :=
  fixedExpFold (2 ^ 192) gaussianExpPower exponent bits

theorem gaussianExpProbability_zero (exponent : Nat) :
    gaussianExpProbability 0 exponent = 2 ^ 192 - 1 := by rfl

/-- Loop step `bits`: `gaussian_fraction_mul` by table entry `bits`, selected by bit `bits`
    of the exponent. -/
theorem gaussianExpProbability_succ (bits exponent : Nat) :
    gaussianExpProbability (bits + 1) exponent =
      if exponent.testBit bits then
        gaussianExpProbability bits exponent * gaussianExpPower bits / 2 ^ 192
      else gaussianExpProbability bits exponent := by rfl

/-- `∏_{i < bits} (if bit i of e is set then g i else pad i)`. With `pad = fun _ => 1` this is
    the product of `g i` over the set bits of `e` below `bits`. -/
def bitSelProd (g pad : Nat → Nat) (e : Nat) : Nat → Nat
  | 0 => 1
  | bits + 1 => bitSelProd g pad e bits * (if e.testBit bits then g bits else pad bits)

/-- Number of set bits of `e` below position `bits`. -/
def bitCount (e : Nat) : Nat → Nat
  | 0 => 0
  | bits + 1 => bitCount e bits + (if e.testBit bits then 1 else 0)

theorem bitSelProd_zero (g pad : Nat → Nat) (e : Nat) : bitSelProd g pad e 0 = 1 := by rfl

theorem bitSelProd_succ (g pad : Nat → Nat) (e bits : Nat) :
    bitSelProd g pad e (bits + 1) =
      bitSelProd g pad e bits * (if e.testBit bits then g bits else pad bits) := by rfl

theorem bitCount_zero (e : Nat) : bitCount e 0 = 0 := by rfl

theorem bitCount_succ (e bits : Nat) :
    bitCount e (bits + 1) = bitCount e bits + (if e.testBit bits then 1 else 0) := by rfl

theorem bitCount_le (e : Nat) : ∀ bits : Nat, bitCount e bits ≤ bits
  | 0 => Nat.le_refl 0
  | bits + 1 => by
    have ih := bitCount_le e bits
    rw [bitCount_succ]
    split <;> omega

theorem bitSelProd_const_pow (Q e : Nat) :
    ∀ bits : Nat, bitSelProd (fun _ => Q) (fun _ => 1) e bits = Q ^ bitCount e bits
  | 0 => rfl
  | bits + 1 => by
    rw [bitSelProd_succ, bitCount_succ, bitSelProd_const_pow Q e bits]
    by_cases hb : e.testBit bits = true
    · rw [ite_eq_left hb, ite_eq_left hb, Nat.pow_succ]
    · rw [ite_eq_right hb, ite_eq_right hb, Nat.mul_one, Nat.add_zero]

theorem bitSelProd_pad_self (g : Nat → Nat) (e : Nat) :
    ∀ bits : Nat, bitSelProd g g e bits = bitSelProd g g 0 bits
  | 0 => rfl
  | bits + 1 => by
    rw [bitSelProd_succ, bitSelProd_succ, bitSelProd_pad_self g e bits]
    by_cases hb : e.testBit bits = true
    · by_cases h0 : (0 : Nat).testBit bits = true
      · rw [ite_eq_left hb, ite_eq_left h0]
      · rw [ite_eq_left hb, ite_eq_right h0]
    · by_cases h0 : (0 : Nat).testBit bits = true
      · rw [ite_eq_right hb, ite_eq_left h0]
      · rw [ite_eq_right hb, ite_eq_right h0]

theorem bitSelProd_pos (g pad : Nat → Nat) (e : Nat) :
    ∀ bits : Nat, (∀ i, i < bits → 0 < g i ∧ 0 < pad i) → 0 < bitSelProd g pad e bits
  | 0, _ => Nat.one_pos
  | bits + 1, hPos => by
    have ih := bitSelProd_pos g pad e bits (fun i hi => hPos i (Nat.lt_succ_of_lt hi))
    have hb := hPos bits (Nat.lt_succ_self bits)
    rw [bitSelProd_succ]
    by_cases hbit : e.testBit bits = true
    · rw [ite_eq_left hbit]; exact Nat.mul_pos ih hb.1
    · rw [ite_eq_right hbit]; exact Nat.mul_pos ih hb.2

/-- One set-bit step of the evaluator against a rational factor `f / d` with
    `t / Q ≤ f / d ≤ (t + 1) / Q`: the running defect grows by at most two units. -/
private theorem fixedExp_step_set (Q p t f d N Dn c : Nat) (hQ : 0 < Q) (hP : p ≤ Q)
    (hT1 : t + 1 ≤ Q) (hTd : t * d ≤ Q * f) (hFd : Q * f ≤ (t + 1) * d)
    (hUp : p * Dn ≤ Q * N) (hLo : Q * N ≤ (p + c) * Dn) :
    p * t / Q ≤ Q ∧ p * t / Q * (Dn * d) ≤ Q * (N * f) ∧
      Q * (N * f) ≤ (p * t / Q + (c + 2)) * (Dn * d) := by
  have hDivLe : p * t / Q * Q ≤ p * t := Nat.div_mul_le_self (p * t) Q
  have hDivLt : p * t < p * t / Q * Q + Q := by
    have hm := Nat.div_add_mod (p * t) Q
    have hr := Nat.mod_lt (p * t) hQ
    have hc : Q * (p * t / Q) = p * t / Q * Q := Nat.mul_comm _ _
    omega
  have hBound : p * t / Q ≤ Q :=
    Nat.div_le_of_le_mul (Nat.mul_le_mul hP (Nat.le_of_succ_le hT1))
  generalize p * t / Q = p' at hDivLe hDivLt hBound ⊢
  refine ⟨hBound, ?_, ?_⟩
  · apply Nat.le_of_mul_le_mul_left _ hQ
    calc Q * (p' * (Dn * d)) = p' * Q * (Dn * d) := by ac_rfl
      _ ≤ p * t * (Dn * d) := Nat.mul_le_mul_right _ hDivLe
      _ = p * Dn * (t * d) := by ac_rfl
      _ ≤ Q * N * (Q * f) := Nat.mul_le_mul hUp hTd
      _ = Q * (Q * (N * f)) := by ac_rfl
  · apply Nat.le_of_mul_le_mul_left _ hQ
    have hCoef : (p + c) * (t + 1) ≤ (p' + (c + 2)) * Q := by
      have e1 : (p + c) * (t + 1) = p * t + p + c * (t + 1) := by
        rw [Nat.add_mul, Nat.mul_add p t 1, Nat.mul_one]
      have e2 : (p' + (c + 2)) * Q = p' * Q + c * Q + 2 * Q := by
        rw [Nat.add_mul, Nat.add_mul, Nat.add_assoc]
      have e3 : c * (t + 1) ≤ c * Q := Nat.mul_le_mul_left c hT1
      omega
    calc Q * (Q * (N * f)) = Q * N * (Q * f) := by ac_rfl
      _ ≤ (p + c) * Dn * ((t + 1) * d) := Nat.mul_le_mul hLo hFd
      _ = (p + c) * (t + 1) * (Dn * d) := by ac_rfl
      _ ≤ (p' + (c + 2)) * Q * (Dn * d) := Nat.mul_le_mul_right _ hCoef
      _ = Q * ((p' + (c + 2)) * (Dn * d)) := by ac_rfl

private theorem fixedExpFold_error (Q : Nat) (hQ : 0 < Q) (tbl f d pad : Nat → Nat) (e : Nat) :
    ∀ bits : Nat,
      (∀ i, i < bits → tbl i + 1 ≤ Q ∧ tbl i * d i ≤ Q * f i ∧ Q * f i ≤ (tbl i + 1) * d i) →
      fixedExpFold Q tbl e bits ≤ Q ∧
      fixedExpFold Q tbl e bits * bitSelProd d pad e bits ≤ Q * bitSelProd f pad e bits ∧
      Q * bitSelProd f pad e bits ≤
        (fixedExpFold Q tbl e bits + (1 + 2 * bitCount e bits)) * bitSelProd d pad e bits
  | 0, _ => by
    refine ⟨Nat.sub_le Q 1, ?_, ?_⟩
    · show (Q - 1) * 1 ≤ Q * 1
      omega
    · show Q * 1 ≤ (Q - 1 + (1 + 2 * 0)) * 1
      omega
  | bits + 1, hTbl => by
    obtain ⟨hP, hUp, hLo⟩ := fixedExpFold_error Q hQ tbl f d pad e bits
      (fun i hi => hTbl i (Nat.lt_succ_of_lt hi))
    obtain ⟨hT1, hTd, hFd⟩ := hTbl bits (Nat.lt_succ_self bits)
    rw [bitSelProd_succ, bitSelProd_succ, bitCount_succ]
    show (if e.testBit bits = true then fixedExpFold Q tbl e bits * tbl bits / Q
          else fixedExpFold Q tbl e bits) ≤ Q ∧
      (if e.testBit bits = true then fixedExpFold Q tbl e bits * tbl bits / Q
          else fixedExpFold Q tbl e bits) *
        (bitSelProd d pad e bits * (if e.testBit bits = true then d bits else pad bits)) ≤
        Q * (bitSelProd f pad e bits * (if e.testBit bits = true then f bits else pad bits)) ∧
      Q * (bitSelProd f pad e bits * (if e.testBit bits = true then f bits else pad bits)) ≤
        ((if e.testBit bits = true then fixedExpFold Q tbl e bits * tbl bits / Q
          else fixedExpFold Q tbl e bits) +
          (1 + 2 * (bitCount e bits + (if e.testBit bits = true then 1 else 0)))) *
        (bitSelProd d pad e bits * (if e.testBit bits = true then d bits else pad bits))
    by_cases hb : e.testBit bits = true
    · have hStep := fixedExp_step_set Q _ _ _ _ _ _ (1 + 2 * bitCount e bits)
        hQ hP hT1 hTd hFd hUp hLo
      have hCnt : 1 + 2 * (bitCount e bits + 1) = 1 + 2 * bitCount e bits + 2 := by omega
      simp only [ite_eq_left hb]
      rw [hCnt]
      exact hStep
    · simp only [ite_eq_right hb, Nat.add_zero]
      refine ⟨hP, ?_, ?_⟩
      · calc fixedExpFold Q tbl e bits * (bitSelProd d pad e bits * pad bits)
            = fixedExpFold Q tbl e bits * bitSelProd d pad e bits * pad bits :=
              (Nat.mul_assoc _ _ _).symm
          _ ≤ Q * bitSelProd f pad e bits * pad bits := Nat.mul_le_mul_right _ hUp
          _ = Q * (bitSelProd f pad e bits * pad bits) := Nat.mul_assoc _ _ _
      · calc Q * (bitSelProd f pad e bits * pad bits)
            = Q * bitSelProd f pad e bits * pad bits := (Nat.mul_assoc _ _ _).symm
          _ ≤ (fixedExpFold Q tbl e bits + (1 + 2 * bitCount e bits)) *
                bitSelProd d pad e bits * pad bits := Nat.mul_le_mul_right _ hLo
          _ = (fixedExpFold Q tbl e bits + (1 + 2 * bitCount e bits)) *
                (bitSelProd d pad e bits * pad bits) := Nat.mul_assoc _ _ _

theorem rlweGaussianExpPowers_length : rlweGaussianExpPowers.length = 30 := by decide

/-- Every table entry is at most `2^192 - 1`, so a unit above it is still a Q192 fraction. -/
theorem gaussianExpPower_succ_le : ∀ i, i < 30 → gaussianExpPower i + 1 ≤ 2 ^ 192 := by
  decide +kernel

/-- Reference values of the evaluator, computed outside Lean from the Rust table by the same
    multiply-and-shift recurrence. -/
theorem gaussianExpProbability_reference_values :
    gaussianExpProbability 24 0 = 2 ^ 192 - 1 ∧
    gaussianExpProbability 24 1 = 0xffffeee161ee8ccb4596fdd04820cdf51e0ee5c166ce3f44 ∧
    gaussianExpProbability 24 490000 = 0x9b4597e37cb04ff3d675a35530cdd767e347bf8ad0e80ab6 ∧
    gaussianExpProbability 24 (3070 * 3070) = 0x45cdf4ca3b0b500f5c61a6620393f837d28bc11242edd ∧
    gaussianExpProbability 24 (3072 * 3072) = 0x44ef5c1ac77a3565239baef4969078b58b3ccc5f84a7b ∧
    gaussianExpProbability 30 3615102 = 0x66666579cb46e142a405162458049acf565b3fa4c3b016b ∧
    gaussianExpProbability 30 (2 ^ 30 - 1) = 0 := by
  decide +kernel

/-- **Evaluator error against a rational factor bracket.** Let `f i / d i` be any fractions
    with `table[i] / 2^192 ≤ f i / d i ≤ (table[i] + 1) / 2^192` for `i < bits ≤ 30`. Then the
    evaluator output `p` satisfies
    `p / 2^192 ≤ ∏ f i / ∏ d i ≤ (p + 1 + 2 * popcount) / 2^192`,
    the products taken over the set bits of `e` below `bits` (and over `pad` elsewhere, on
    both sides). -/
theorem gaussianExpProbability_bracket (bits : Nat) (hBits : bits ≤ 30) (e : Nat)
    (f d pad : Nat → Nat)
    (hBracket : ∀ i, i < bits →
      gaussianExpPower i * d i ≤ 2 ^ 192 * f i ∧ 2 ^ 192 * f i ≤ (gaussianExpPower i + 1) * d i) :
    gaussianExpProbability bits e * bitSelProd d pad e bits ≤ 2 ^ 192 * bitSelProd f pad e bits ∧
    2 ^ 192 * bitSelProd f pad e bits ≤
      (gaussianExpProbability bits e + (1 + 2 * bitCount e bits)) * bitSelProd d pad e bits :=
  (fixedExpFold_error (2 ^ 192) (Nat.two_pow_pos 192) gaussianExpPower f d pad e bits
    (fun i hi => ⟨gaussianExpPower_succ_le i (Nat.lt_of_lt_of_le hi hBits), hBracket i hi⟩)).2

/-- The evaluator output is a Q192 fraction. -/
theorem gaussianExpProbability_le (bits : Nat) (hBits : bits ≤ 30) (e : Nat) :
    gaussianExpProbability bits e ≤ 2 ^ 192 :=
  (fixedExpFold_error (2 ^ 192) (Nat.two_pow_pos 192) gaussianExpPower gaussianExpPower
    (fun _ => 2 ^ 192) (fun _ => 1) e bits
    (fun i hi => ⟨gaussianExpPower_succ_le i (Nat.lt_of_lt_of_le hi hBits),
      Nat.le_of_eq (Nat.mul_comm _ _),
      Nat.le_trans (Nat.le_of_eq (Nat.mul_comm _ _))
        (Nat.mul_le_mul_right _ (Nat.le_succ _))⟩)).1

/-! ## 2. Finite summation operators and cross-multiplied L1 distance -/

private theorem nad_le {a b c : Nat} (h1 : a ≤ b + c) (h2 : b ≤ a + c) :
    Spec.natAbsDiff a b ≤ c := by
  unfold Spec.natAbsDiff
  split <;> omega

private theorem le_add_nad (a b : Nat) : a ≤ b + Spec.natAbsDiff a b := by
  unfold Spec.natAbsDiff
  split <;> omega

private theorem le_add_nad' (a b : Nat) : b ≤ a + Spec.natAbsDiff a b := by
  unfold Spec.natAbsDiff
  split <;> omega

private theorem nad_mul_right (a b c : Nat) :
    Spec.natAbsDiff (a * c) (b * c) = Spec.natAbsDiff a b * c := by
  unfold Spec.natAbsDiff
  by_cases h : a ≤ b
  · rw [ite_eq_left h, ite_eq_left (Nat.mul_le_mul_right c h), Nat.sub_mul]
  · have hba : b * c ≤ a * c := Nat.mul_le_mul_right c (Nat.le_of_lt (Nat.lt_of_not_le h))
    by_cases h' : a * c ≤ b * c
    · rw [ite_eq_right h, ite_eq_left h', Nat.sub_mul]
      omega
    · rw [ite_eq_right h, ite_eq_right h', Nat.sub_mul]

private theorem nad_mul_right_of {a b c u v : Nat} (hu : u = a * c) (hv : v = b * c) :
    Spec.natAbsDiff u v = Spec.natAbsDiff a b * c := by
  rw [hu, hv]
  exact nad_mul_right a b c

private theorem nad_mul_left_of {a b c u v : Nat} (hu : u = c * a) (hv : v = c * b) :
    Spec.natAbsDiff u v = c * Spec.natAbsDiff a b := by
  rw [hu, hv, Nat.mul_comm c a, Nat.mul_comm c b, Nat.mul_comm c]
  exact nad_mul_right a b c

private theorem nad_eq_of_add_eq {a b c d : Nat} (h : a + c = b + d) :
    Spec.natAbsDiff a b = Spec.natAbsDiff c d := by
  unfold Spec.natAbsDiff
  split <;> split <;> omega

/-- A finite summation operator on `α → Nat`: additive and monotone. `Spec.sampleSum n` is one,
    and so is every iterated sum built from such operators. -/
structure IsFinSum {α : Type} (S : (α → Nat) → Nat) : Prop where
  add : ∀ f g : α → Nat, S (fun x => f x + g x) = S f + S g
  mono : ∀ f g : α → Nat, (∀ x, f x ≤ g x) → S f ≤ S g

theorem IsFinSum.zero {α : Type} {S : (α → Nat) → Nat} (hS : IsFinSum S) :
    S (fun _ => 0) = 0 := by
  have h : S (fun _ : α => 0) = S (fun _ : α => 0) + S (fun _ : α => 0) :=
    hS.add (fun _ => 0) (fun _ => 0)
  omega

theorem IsFinSum.mul_left {α : Type} {S : (α → Nat) → Nat} (hS : IsFinSum S) (c : Nat)
    (f : α → Nat) : S (fun x => c * f x) = c * S f := by
  induction c with
  | zero =>
    have h : (fun x => 0 * f x) = (fun _ : α => 0) := funext (fun x => Nat.zero_mul (f x))
    rw [h, hS.zero, Nat.zero_mul]
  | succ c ih =>
    have h : (fun x => (c + 1) * f x) = (fun x => c * f x + f x) :=
      funext (fun x => Nat.succ_mul c (f x))
    rw [h, hS.add (fun x => c * f x) f, ih, Nat.succ_mul]

theorem IsFinSum.mul_right {α : Type} {S : (α → Nat) → Nat} (hS : IsFinSum S) (f : α → Nat)
    (c : Nat) : S (fun x => f x * c) = S f * c := by
  have h : (fun x => f x * c) = (fun x => c * f x) := funext (fun x => Nat.mul_comm (f x) c)
  rw [h, hS.mul_left c f, Nat.mul_comm]

theorem IsFinSum.const {α : Type} {S : (α → Nat) → Nat} (hS : IsFinSum S) (c : Nat) :
    S (fun _ => c) = c * S (fun _ => 1) := by
  have h : (fun _ : α => c) = (fun _ : α => c * 1) := funext (fun _ => (Nat.mul_one c).symm)
  exact (congrArg S h).trans (hS.mul_left c (fun _ => 1))

theorem IsFinSum.natAbsDiff_le {α : Type} {S : (α → Nat) → Nat} (hS : IsFinSum S)
    (f g : α → Nat) :
    Spec.natAbsDiff (S f) (S g) ≤ S (fun x => Spec.natAbsDiff (f x) (g x)) := by
  have h1 : S f ≤ S g + S (fun x => Spec.natAbsDiff (f x) (g x)) :=
    Nat.le_trans (hS.mono f (fun x => g x + Spec.natAbsDiff (f x) (g x))
      (fun x => le_add_nad (f x) (g x)))
      (Nat.le_of_eq (hS.add g (fun x => Spec.natAbsDiff (f x) (g x))))
  have h2 : S g ≤ S f + S (fun x => Spec.natAbsDiff (f x) (g x)) :=
    Nat.le_trans (hS.mono g (fun x => f x + Spec.natAbsDiff (f x) (g x))
      (fun x => le_add_nad' (f x) (g x)))
      (Nat.le_of_eq (hS.add f (fun x => Spec.natAbsDiff (f x) (g x))))
  exact nad_le h1 h2

/-- Splitting a sum along an event and its complement. -/
theorem IsFinSum.split {α : Type} {S : (α → Nat) → Nat} (hS : IsFinSum S) (f : α → Nat)
    (E : α → Bool) :
    S f = S (fun x => if E x then f x else 0) + S (fun x => if E x then 0 else f x) := by
  rw [← hS.add (fun x => if E x then f x else 0) (fun x => if E x then 0 else f x)]
  refine congrArg S (funext fun x => ?_)
  by_cases h : E x = true
  · rw [ite_eq_left h, ite_eq_left h]
    omega
  · rw [ite_eq_right h, ite_eq_right h]
    omega

/-- Iterated sums are summation operators on any pairing of the two index types. -/
theorem IsFinSum.nest {α β γ : Type} {S : (α → Nat) → Nat} {T : (β → Nat) → Nat}
    (hS : IsFinSum S) (hT : IsFinSum T) (pair : α → β → γ) :
    IsFinSum (fun F : γ → Nat => S (fun x => T (fun y => F (pair x y)))) where
  add f g := by
    have h : (fun x => T (fun y => f (pair x y) + g (pair x y))) =
        (fun x => T (fun y => f (pair x y)) + T (fun y => g (pair x y))) :=
      funext (fun x => hT.add (fun y => f (pair x y)) (fun y => g (pair x y)))
    show S (fun x => T (fun y => f (pair x y) + g (pair x y))) = _
    rw [h]
    exact hS.add (fun x => T (fun y => f (pair x y))) (fun x => T (fun y => g (pair x y)))
  mono f g hfg :=
    hS.mono _ _ (fun x => hT.mono _ _ (fun y => hfg (pair x y)))

private theorem sampleSum_add' :
    ∀ (n : Nat) (f g : Fin n → Nat),
      Spec.sampleSum n (fun i => f i + g i) = Spec.sampleSum n f + Spec.sampleSum n g
  | 0, _, _ => by rfl
  | n + 1, f, g => by
    have ih := sampleSum_add' n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    rw [Spec.sampleSum_succ n f, Spec.sampleSum_succ n g]
    show f ⟨0, Nat.zero_lt_succ n⟩ + g ⟨0, Nat.zero_lt_succ n⟩ +
      Spec.sampleSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ +
        g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) = _
    rw [ih]
    omega

private theorem sampleSum_mono' :
    ∀ (n : Nat) (f g : Fin n → Nat), (∀ i, f i ≤ g i) →
      Spec.sampleSum n f ≤ Spec.sampleSum n g
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, f, g, h => by
    rw [Spec.sampleSum_succ n f, Spec.sampleSum_succ n g]
    exact Nat.add_le_add (h ⟨0, Nat.zero_lt_succ n⟩)
      (sampleSum_mono' n _ _ (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

theorem sampleSum_isFinSum (n : Nat) : IsFinSum (Spec.sampleSum n) where
  add := sampleSum_add' n
  mono := sampleSum_mono' n

private theorem sampleSum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    Spec.sampleSum n f = Spec.sampleSum n g :=
  congrArg (Spec.sampleSum n) (funext h)

/-- Sum over `Fin n` of a function of the index value. -/
@[expose] def coordSum (n : Nat) (g : Nat → Nat) : Nat := Spec.sampleSum n (fun i => g i.val)

theorem coordSum_succ : ∀ (n : Nat) (g : Nat → Nat), coordSum (n + 1) g = coordSum n g + g n
  | 0, g => by
    show g 0 + 0 = 0 + g 0
    omega
  | n + 1, g => by
    have h1 : coordSum (n + 2) g = g 0 + coordSum (n + 1) (fun j => g (j + 1)) := by rfl
    have h2 := coordSum_succ n (fun j => g (j + 1))
    have h3 : coordSum (n + 1) g = g 0 + coordSum n (fun j => g (j + 1)) := by rfl
    rw [h1, h2, h3]
    omega

theorem coordSum_isFinSum (n : Nat) : IsFinSum (coordSum n) where
  add f g := (sampleSum_isFinSum n).add (fun i => f i.val) (fun i => g i.val)
  mono f g h := (sampleSum_isFinSum n).mono (fun i => f i.val) (fun i => g i.val) (fun i => h i.val)

theorem coordSum_one : ∀ n : Nat, coordSum n (fun _ => 1) = n
  | 0 => by rfl
  | n + 1 => by rw [coordSum_succ, coordSum_one n]

/-- `∑_{i < n} [i < p] = min p n`. -/
theorem coordSum_lt_indicator (p : Nat) :
    ∀ n : Nat, coordSum n (fun i => if i < p then 1 else 0) = min p n
  | 0 => by
    show 0 = min p 0
    omega
  | n + 1 => by
    rw [coordSum_succ, coordSum_lt_indicator p n]
    split <;> omega

/-- `∑_{i < n} [i = j] * c = [j < n] * c`. -/
theorem coordSum_point_indicator (j c : Nat) :
    ∀ n : Nat, coordSum n (fun i => if i = j then c else 0) = if j < n then c else 0
  | 0 => by
    show 0 = if j < 0 then c else 0
    rw [ite_eq_right (Nat.not_lt_zero j)]
  | n + 1 => by
    rw [coordSum_succ, coordSum_point_indicator j c n]
    split <;> split <;> split <;> omega

/-- Restricting a sum over `N` indices to its first `n ≤ N`. -/
theorem coordSum_truncate (n : Nat) (g : Nat → Nat) :
    ∀ N : Nat, n ≤ N → coordSum N (fun i => if i < n then g i else 0) = coordSum n g
  | 0, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | N + 1, h => by
    rw [coordSum_succ]
    by_cases hN : n ≤ N
    · rw [coordSum_truncate n g N hN, ite_eq_right (by omega : ¬ N < n)]
      omega
    · have hn : n = N + 1 := by omega
      subst hn
      rw [ite_eq_left (Nat.lt_succ_self N), coordSum_succ]
      have hEq : coordSum N (fun i => if i < N + 1 then g i else 0) = coordSum N g :=
        sampleSum_congr (fun i => ite_eq_left (Nat.lt_succ_of_lt i.isLt))
      rw [hEq]

/-- Back-to-front partial sums: the form in which the kernel evaluates a concrete total. -/
def weightPrefixSum (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => weightPrefixSum g n + g n

theorem coordSum_eq_weightPrefixSum (g : Nat → Nat) :
    ∀ n : Nat, coordSum n g = weightPrefixSum g n
  | 0 => by rfl
  | n + 1 => by
    rw [coordSum_succ, coordSum_eq_weightPrefixSum g n]
    rfl

/-- **Total-variation bound from a pointwise bracket.** If, after a common rescaling `D / c`,
    the weights `b` lie between `a` and `a + k` pointwise, then
    `∑ |a x * B - b x * A| ≤ 2 * (N * k) * B`, where `A`, `B` are the two totals and `N` the
    number of outcomes. Dividing by `2 * A * B` reads `TV(a / A, b / B) ≤ N * k / A`. -/
theorem IsFinSum.cross_l1_le_of_bracket {α : Type} {S : (α → Nat) → Nat} (hS : IsFinSum S)
    (a b : α → Nat) (c D k : Nat) (hc : 0 < c)
    (hLo : ∀ x, a x * D ≤ c * b x) (hHi : ∀ x, c * b x ≤ (a x + k) * D) :
    S (fun x => Spec.natAbsDiff (a x * S b) (b x * S a)) ≤ 2 * (S (fun _ => 1) * k) * S b := by
  have hAD : S a * D ≤ c * S b :=
    calc S a * D = S (fun x => a x * D) := (hS.mul_right a D).symm
      _ ≤ S (fun x => c * b x) := hS.mono _ _ hLo
      _ = c * S b := hS.mul_left c b
  have hcB : c * S b ≤ (S a + k * S (fun _ => 1)) * D :=
    calc c * S b = S (fun x => c * b x) := (hS.mul_left c b).symm
      _ ≤ S (fun x => (a x + k) * D) := hS.mono _ _ hHi
      _ = S (fun x => a x + k) * D := hS.mul_right (fun x => a x + k) D
      _ = (S a + S (fun _ => k)) * D := by rw [hS.add a (fun _ => k)]
      _ = (S a + k * S (fun _ => 1)) * D := by rw [hS.const k]
  have hPt : ∀ x, c * Spec.natAbsDiff (a x * S b) (b x * S a) ≤
      a x * (k * S (fun _ => 1) * D) + k * D * S a := by
    intro x
    have h1 : a x * D * S a ≤ c * b x * S a := Nat.mul_le_mul_right (S a) (hLo x)
    have h2 : c * b x * S a ≤ a x * D * S a + k * D * S a := by
      have h := Nat.mul_le_mul_right (S a) (hHi x)
      rw [Nat.add_mul (a x) k D, Nat.add_mul] at h
      exact h
    have h3 : a x * D * S a ≤ a x * (c * S b) := by
      have h := Nat.mul_le_mul_left (a x) hAD
      have e : a x * D * S a = a x * (S a * D) := by ac_rfl
      omega
    have h4 : a x * (c * S b) ≤ a x * D * S a + a x * (k * S (fun _ => 1) * D) := by
      have h := Nat.mul_le_mul_left (a x) hcB
      have e : a x * ((S a + k * S (fun _ => 1)) * D) =
          a x * D * S a + a x * (k * S (fun _ => 1) * D) := by
        rw [Nat.add_mul, Nat.mul_add]
        congr 1
        ac_rfl
      omega
    have e0 : c * Spec.natAbsDiff (a x * S b) (b x * S a) =
        Spec.natAbsDiff (a x * (c * S b)) (c * b x * S a) :=
      (nad_mul_left_of (by ac_rfl) (by ac_rfl)).symm
    rw [e0]
    exact nad_le (by omega) (by omega)
  have hSum : c * S (fun x => Spec.natAbsDiff (a x * S b) (b x * S a)) ≤
      S a * (k * S (fun _ => 1) * D) + k * D * S a * S (fun _ => 1) :=
    calc c * S (fun x => Spec.natAbsDiff (a x * S b) (b x * S a))
        = S (fun x => c * Spec.natAbsDiff (a x * S b) (b x * S a)) := (hS.mul_left c _).symm
      _ ≤ S (fun x => a x * (k * S (fun _ => 1) * D) + k * D * S a) := hS.mono _ _ hPt
      _ = S (fun x => a x * (k * S (fun _ => 1) * D)) + S (fun _ => k * D * S a) :=
          hS.add (fun x => a x * (k * S (fun _ => 1) * D)) (fun _ => k * D * S a)
      _ = S a * (k * S (fun _ => 1) * D) + k * D * S a * S (fun _ => 1) := by
          rw [hS.mul_right a (k * S (fun _ => 1) * D), hS.const (k * D * S a)]
  apply Nat.le_of_mul_le_mul_left _ hc
  have e1 : S a * (k * S (fun _ => 1) * D) = S (fun _ => 1) * k * (S a * D) := by ac_rfl
  have e2 : k * D * S a * S (fun _ => 1) = S (fun _ => 1) * k * (S a * D) := by ac_rfl
  have e3 : c * (2 * (S (fun _ => 1) * k) * S b) = 2 * (S (fun _ => 1) * k * (c * S b)) := by
    ac_rfl
  have h5 : S (fun _ => 1) * k * (S a * D) ≤ S (fun _ => 1) * k * (c * S b) :=
    Nat.mul_le_mul_left _ hAD
  omega

/-- Under the lower half of a bracket the totals satisfy `A * D ≤ c * B`. -/
theorem IsFinSum.total_le_of_bracket {α : Type} {S : (α → Nat) → Nat} (hS : IsFinSum S)
    (a b : α → Nat) (c D : Nat) (hLo : ∀ x, a x * D ≤ c * b x) : S a * D ≤ c * S b :=
  calc S a * D = S (fun x => a x * D) := (hS.mul_right a D).symm
    _ ≤ S (fun x => c * b x) := hS.mono _ _ hLo
    _ = c * S b := hS.mul_left c b

/-- **Subadditivity of total variation under products.** For weights `a, b` on `α` and
    `a', b'` on `β`, the cross-multiplied L1 distance of the product weights is at most
    `L1(a, b) * (A' * B') + (A * B) * L1(a', b')`. Dividing by `2 * A * A' * B * B'` reads
    `TV(a ⊗ a', b ⊗ b') ≤ TV(a, b) + TV(a', b')`. -/
theorem IsFinSum.cross_l1_prod_le {α β : Type} {S : (α → Nat) → Nat} {T : (β → Nat) → Nat}
    (hS : IsFinSum S) (hT : IsFinSum T) (a b : α → Nat) (a' b' : β → Nat) :
    S (fun x => T (fun y =>
        Spec.natAbsDiff (a x * a' y * (S b * T b')) (b x * b' y * (S a * T a')))) ≤
      S (fun x => Spec.natAbsDiff (a x * S b) (b x * S a)) * (T a' * T b') +
        S a * S b * T (fun y => Spec.natAbsDiff (a' y * T b') (b' y * T a')) := by
  have hPt : ∀ x y,
      Spec.natAbsDiff (a x * a' y * (S b * T b')) (b x * b' y * (S a * T a')) ≤
        Spec.natAbsDiff (a x * S b) (b x * S a) * (a' y * T b') +
          b x * S a * Spec.natAbsDiff (a' y * T b') (b' y * T a') := by
    intro x y
    have tri := Spec.natAbsDiff_triangle (a x * a' y * (S b * T b'))
      (b x * a' y * (S a * T b')) (b x * b' y * (S a * T a'))
    have e1 : Spec.natAbsDiff (a x * a' y * (S b * T b')) (b x * a' y * (S a * T b')) =
        Spec.natAbsDiff (a x * S b) (b x * S a) * (a' y * T b') :=
      nad_mul_right_of (by ac_rfl) (by ac_rfl)
    have e2 : Spec.natAbsDiff (b x * a' y * (S a * T b')) (b x * b' y * (S a * T a')) =
        b x * S a * Spec.natAbsDiff (a' y * T b') (b' y * T a') :=
      nad_mul_left_of (by ac_rfl) (by ac_rfl)
    rw [e1, e2] at tri
    exact tri
  have hInner : ∀ x,
      T (fun y => Spec.natAbsDiff (a x * a' y * (S b * T b')) (b x * b' y * (S a * T a'))) ≤
        Spec.natAbsDiff (a x * S b) (b x * S a) * (T a' * T b') +
          b x * (S a * T (fun y => Spec.natAbsDiff (a' y * T b') (b' y * T a'))) := by
    intro x
    refine Nat.le_trans (hT.mono _ _ (hPt x)) (Nat.le_of_eq ?_)
    rw [hT.add (fun y => Spec.natAbsDiff (a x * S b) (b x * S a) * (a' y * T b'))
        (fun y => b x * S a * Spec.natAbsDiff (a' y * T b') (b' y * T a')),
      hT.mul_left (Spec.natAbsDiff (a x * S b) (b x * S a)) (fun y => a' y * T b'),
      hT.mul_right a' (T b'),
      hT.mul_left (b x * S a) (fun y => Spec.natAbsDiff (a' y * T b') (b' y * T a')),
      Nat.mul_assoc (b x) (S a)]
  refine Nat.le_trans (hS.mono _ _ hInner) (Nat.le_of_eq ?_)
  rw [hS.add (fun x => Spec.natAbsDiff (a x * S b) (b x * S a) * (T a' * T b'))
      (fun x => b x * (S a * T (fun y => Spec.natAbsDiff (a' y * T b') (b' y * T a')))),
    hS.mul_right (fun x => Spec.natAbsDiff (a x * S b) (b x * S a)) (T a' * T b'),
    hS.mul_right b (S a * T (fun y => Spec.natAbsDiff (a' y * T b') (b' y * T a')))]
  congr 1
  ac_rfl

private theorem event_core (aE aN bE bN A B LE LN : Nat) (hA : A = aE + aN) (hB : B = bE + bN)
    (h1 : Spec.natAbsDiff (aE * B) (bE * A) ≤ LE)
    (h2 : Spec.natAbsDiff (aN * B) (bN * A) ≤ LN) :
    2 * Spec.natAbsDiff (aE * B) (bE * A) ≤ LE + LN := by
  have hSum : aE * B + aN * B = bE * A + bN * A := by
    rw [← Nat.add_mul, ← Nat.add_mul, ← hA, ← hB]
    exact Nat.mul_comm A B
  have hEq := nad_eq_of_add_eq hSum
  omega

/-- **Event probabilities transfer.** For every event `E`,
    `2 * |a(E) * B - b(E) * A| ≤ ∑ |a x * B - b x * A|`; dividing by `2 * A * B` reads
    `|P_a(E) - P_b(E)| ≤ TV(P_a, P_b)`. -/
theorem IsFinSum.event_cross_le {α : Type} {S : (α → Nat) → Nat} (hS : IsFinSum S)
    (a b : α → Nat) (E : α → Bool) :
    2 * Spec.natAbsDiff (S (fun x => if E x then a x else 0) * S b)
        (S (fun x => if E x then b x else 0) * S a) ≤
      S (fun x => Spec.natAbsDiff (a x * S b) (b x * S a)) := by
  have h1 : Spec.natAbsDiff (S (fun x => if E x then a x else 0) * S b)
      (S (fun x => if E x then b x else 0) * S a) ≤
      S (fun x => if E x then Spec.natAbsDiff (a x * S b) (b x * S a) else 0) := by
    rw [← hS.mul_right (fun x => if E x then a x else 0) (S b),
      ← hS.mul_right (fun x => if E x then b x else 0) (S a)]
    refine Nat.le_trans (hS.natAbsDiff_le _ _) (Nat.le_of_eq (congrArg S (funext fun x => ?_)))
    by_cases h : E x = true
    · simp only [ite_eq_left h]
    · simp only [ite_eq_right h, Nat.zero_mul]
      rfl
  have h2 : Spec.natAbsDiff (S (fun x => if E x then 0 else a x) * S b)
      (S (fun x => if E x then 0 else b x) * S a) ≤
      S (fun x => if E x then 0 else Spec.natAbsDiff (a x * S b) (b x * S a)) := by
    rw [← hS.mul_right (fun x => if E x then 0 else a x) (S b),
      ← hS.mul_right (fun x => if E x then 0 else b x) (S a)]
    refine Nat.le_trans (hS.natAbsDiff_le _ _) (Nat.le_of_eq (congrArg S (funext fun x => ?_)))
    by_cases h : E x = true
    · simp only [ite_eq_left h, Nat.zero_mul]
      rfl
    · simp only [ite_eq_right h]
  rw [hS.split (fun x => Spec.natAbsDiff (a x * S b) (b x * S a)) E]
  exact event_core _ _ _ _ _ _ _ _ (hS.split a E) (hS.split b E) h1 h2

/-! ## 3. The threshold comparison as a finite game -/

/-- Game over `n` equally likely coins won when the coin is below the threshold `p`. -/
@[expose] def thresholdGame (n : Nat) (hn : 0 < n) (p : Nat) : Spec.FinGame n :=
  ⟨hn, fun u => decide (u.val < p)⟩

/-- `gaussian_fraction_lt(random, probability)`: accept iff the 192-bit coin is below the
    threshold. -/
@[expose] def q192BernoulliAccept (p192 : Nat) (u : Fin (2 ^ 192)) : Bool := decide (u.val < p192)

/-- The Q192 Bernoulli step as a game over the `2^192` values of the coin. -/
@[expose] def q192BernoulliGame (p192 : Nat) : Spec.FinGame (2 ^ 192) :=
  ⟨Nat.two_pow_pos 192, q192BernoulliAccept p192⟩

/-- Exactly `min p n` of the `n` coins are below the threshold `p`. -/
theorem thresholdGame_winCount (n : Nat) (hn : 0 < n) (p : Nat) :
    (thresholdGame n hn p).winCount = min p n := by
  rw [← coordSum_lt_indicator p n]
  show Spec.sampleSum n (fun u : Fin n => if decide (u.val < p) = true then 1 else 0) =
    Spec.sampleSum n (fun u : Fin n => if u.val < p then 1 else 0)
  refine sampleSum_congr (fun u => ?_)
  by_cases h : u.val < p
  · rw [ite_eq_left h, ite_eq_left (decide_eq_true h)]
  · rw [ite_eq_right h, ite_eq_right (fun hd => h (of_decide_eq_true hd))]

/-- `Spec.sampleSum (2^192) (fun u => if u.val < p then 1 else 0) = p` for a Q192 threshold. -/
theorem q192_accepting_coin_count (p192 : Nat) (hp : p192 ≤ 2 ^ 192) :
    Spec.sampleSum (2 ^ 192) (fun u : Fin (2 ^ 192) => if u.val < p192 then 1 else 0) = p192 :=
  (coordSum_lt_indicator p192 (2 ^ 192)).trans (Nat.min_eq_left hp)

theorem q192BernoulliGame_winCount (p192 : Nat) (hp : p192 ≤ 2 ^ 192) :
    (q192BernoulliGame p192).winCount = p192 :=
  (thresholdGame_winCount (2 ^ 192) (Nat.two_pow_pos 192) p192).trans (Nat.min_eq_left hp)

/-- `Pr[accept] = p192 / 2^192`. -/
theorem q192BernoulliGame_winProb (p192 : Nat) (hp : p192 ≤ 2 ^ 192) :
    (q192BernoulliGame p192).winProb = ⟨p192, 2 ^ 192, Nat.two_pow_pos 192⟩ :=
  Spec.RatBound.ext (q192BernoulliGame_winCount p192 hp) (by rfl)

/-- The Q64 fast-accept / fast-reject filter of the production sampler returns the same bit
    as the Q192 comparison whenever its two bounds enclose the threshold. -/
theorem q192BernoulliAccept_eq_fastFiltered (pLo64 pHi64 p192 : Nat) (u : Fin (2 ^ 192))
    (hLo : pLo64 * 2 ^ 128 ≤ p192) (hHi : p192 ≤ pHi64 * 2 ^ 128) :
    q64FastFilteredBernoulli pLo64 pHi64 p192 u.val = q192BernoulliAccept p192 u :=
  q64FastFilteredBernoulli_eq_exact pLo64 pHi64 p192 u.val hLo hHi

/-- **Pointwise error of the production Bernoulli step (24 exponent bits).** Let `f` be any
    integer factors with `table[i] ≤ f i ≤ table[i] + 1` for `i < 24`, and let
    `ideal / (2^192)^k` be the product of `f i / 2^192` over the `k` set bits of `e` below 24.
    The number `acc` of accepting coins of the Q192 comparison against
    `gaussianExpProbability 24 e` satisfies
    `acc / 2^192 ≤ ideal / (2^192)^k ≤ (acc + 49) / 2^192`. -/
theorem q192_sampler_pointwise_error_le_pow2_neg192 (e : Nat) (f : Nat → Nat)
    (hBracket : ∀ i, i < 24 → gaussianExpPower i ≤ f i ∧ f i ≤ gaussianExpPower i + 1) :
    (q192BernoulliGame (gaussianExpProbability 24 e)).winCount * (2 ^ 192) ^ bitCount e 24 ≤
        2 ^ 192 * bitSelProd f (fun _ => 1) e 24 ∧
    2 ^ 192 * bitSelProd f (fun _ => 1) e 24 ≤
        ((q192BernoulliGame (gaussianExpProbability 24 e)).winCount + 49) *
          (2 ^ 192) ^ bitCount e 24 := by
  rw [q192BernoulliGame_winCount _ (gaussianExpProbability_le 24 (by decide) e)]
  have hB := gaussianExpProbability_bracket 24 (by decide) e f (fun _ => 2 ^ 192) (fun _ => 1)
    (fun i hi =>
      ⟨Nat.le_trans (Nat.mul_le_mul_right (2 ^ 192) (hBracket i hi).1)
          (Nat.le_of_eq (Nat.mul_comm _ _)),
        Nat.le_trans (Nat.le_of_eq (Nat.mul_comm _ _))
          (Nat.mul_le_mul_right (2 ^ 192) (hBracket i hi).2)⟩)
  rw [bitSelProd_const_pow] at hB
  refine ⟨hB.1, Nat.le_trans hB.2 (Nat.mul_le_mul_right _ ?_)⟩
  have hCnt := bitCount_le e 24
  omega

private theorem ratBound_bracket_arith (wc I K Q : Nat) (h2 : Q * I ≤ (wc + 49) * K) :
    I * (Q * Q) ≤ (wc * Q + 49 * Q) * K :=
  calc I * (Q * Q) = Q * I * Q := by ac_rfl
    _ ≤ (wc + 49) * K * Q := Nat.mul_le_mul_right _ h2
    _ = (wc * Q + 49 * Q) * K := by
        rw [← Nat.add_mul]
        ac_rfl

/-- The same statement on `Spec.RatBound`: `Pr[accept] ≤ ideal ≤ Pr[accept] + 49 / 2^192`,
    with `Pr[accept]` the win probability of the Q192 Bernoulli game. -/
theorem q192_sampler_pointwise_error_ratBound (e : Nat) (f : Nat → Nat)
    (hBracket : ∀ i, i < 24 → gaussianExpPower i ≤ f i ∧ f i ≤ gaussianExpPower i + 1) :
    (q192BernoulliGame (gaussianExpProbability 24 e)).winProb.le
        ⟨bitSelProd f (fun _ => 1) e 24, (2 ^ 192) ^ bitCount e 24,
          Nat.pow_pos (Nat.two_pow_pos 192)⟩ ∧
    Spec.RatBound.le
        ⟨bitSelProd f (fun _ => 1) e 24, (2 ^ 192) ^ bitCount e 24,
          Nat.pow_pos (Nat.two_pow_pos 192)⟩
        ((q192BernoulliGame (gaussianExpProbability 24 e)).winProb.add
          ⟨49, 2 ^ 192, Nat.two_pow_pos 192⟩) := by
  obtain ⟨h1, h2⟩ := q192_sampler_pointwise_error_le_pow2_neg192 e f hBracket
  refine ⟨?_, ?_⟩
  · show (q192BernoulliGame (gaussianExpProbability 24 e)).winCount * (2 ^ 192) ^ bitCount e 24 ≤
      bitSelProd f (fun _ => 1) e 24 * 2 ^ 192
    rw [Nat.mul_comm (bitSelProd f (fun _ => 1) e 24)]
    exact h1
  · show bitSelProd f (fun _ => 1) e 24 * (2 ^ 192 * 2 ^ 192) ≤
      ((q192BernoulliGame (gaussianExpProbability 24 e)).winCount * 2 ^ 192 + 49 * 2 ^ 192) *
        (2 ^ 192) ^ bitCount e 24
    exact ratBound_bracket_arith _ _ _ _ h2

/-- The 30-bit evaluator used by `gaussian_accept`: the same statement with `61 = 1 + 2 * 30`
    units. -/
theorem q192_gaussian_accept_pointwise_error_61_ulp (e : Nat) (f : Nat → Nat)
    (hBracket : ∀ i, i < 30 → gaussianExpPower i ≤ f i ∧ f i ≤ gaussianExpPower i + 1) :
    (q192BernoulliGame (gaussianExpProbability 30 e)).winCount * (2 ^ 192) ^ bitCount e 30 ≤
        2 ^ 192 * bitSelProd f (fun _ => 1) e 30 ∧
    2 ^ 192 * bitSelProd f (fun _ => 1) e 30 ≤
        ((q192BernoulliGame (gaussianExpProbability 30 e)).winCount + 61) *
          (2 ^ 192) ^ bitCount e 30 := by
  rw [q192BernoulliGame_winCount _ (gaussianExpProbability_le 30 (by decide) e)]
  have hB := gaussianExpProbability_bracket 30 (by decide) e f (fun _ => 2 ^ 192) (fun _ => 1)
    (fun i hi =>
      ⟨Nat.le_trans (Nat.mul_le_mul_right (2 ^ 192) (hBracket i hi).1)
          (Nat.le_of_eq (Nat.mul_comm _ _)),
        Nat.le_trans (Nat.le_of_eq (Nat.mul_comm _ _))
          (Nat.mul_le_mul_right (2 ^ 192) (hBracket i hi).2)⟩)
  rw [bitSelProd_const_pow] at hB
  refine ⟨hB.1, Nat.le_trans hB.2 (Nat.mul_le_mul_right _ ?_)⟩
  have hCnt := bitCount_le e 30
  omega

/-! ## 4. Finite products of coordinates -/

/-- One coordinate with `size` outcomes `0, …, size - 1` and two weight vectors on them:
    `impl` (the law a sampler realises, up to normalisation) and `ideal` (the law it is
    compared with). -/
structure WeightPair where
  size : Nat
  impl : Nat → Nat
  ideal : Nat → Nat

/-- Sum of `F` over all outcome vectors of a list of coordinates (head coordinate first). -/
@[expose] def jointSum : List WeightPair → (List Nat → Nat) → Nat
  | [], F => F []
  | p :: ps, F => Spec.sampleSum p.size (fun x => jointSum ps (fun v => F (x.val :: v)))

/-- Product weight of an outcome vector; `sel` picks `WeightPair.impl` or `WeightPair.ideal`. -/
@[expose] def jointWeight (sel : WeightPair → Nat → Nat) : List WeightPair → List Nat → Nat
  | [], _ => 1
  | p :: ps, v => sel p (v.headD 0) * jointWeight sel ps v.tail

/-- Product of the per-coordinate totals. -/
@[expose] def jointTotal (sel : WeightPair → Nat → Nat) : List WeightPair → Nat
  | [] => 1
  | p :: ps => coordSum p.size (sel p) * jointTotal sel ps

/-- Cross-multiplied L1 distance of one coordinate: `∑_i |impl i * B - ideal i * A|` with
    `A`, `B` the totals of `impl`, `ideal`. The total-variation distance of the two normalised
    laws is this number divided by `2 * A * B`. -/
def coordL1 (p : WeightPair) : Nat :=
  coordSum p.size (fun i =>
    Spec.natAbsDiff (p.impl i * coordSum p.size p.ideal) (p.ideal i * coordSum p.size p.impl))

/-- Cross-multiplied L1 distance of the two product laws of a list of coordinates. -/
def jointL1 (ps : List WeightPair) : Nat :=
  jointSum ps (fun v =>
    Spec.natAbsDiff (jointWeight WeightPair.impl ps v * jointTotal WeightPair.ideal ps)
      (jointWeight WeightPair.ideal ps v * jointTotal WeightPair.impl ps))

/-- Unnormalised mass of an event on one coordinate. -/
def coordEventMass (n : Nat) (w : Nat → Nat) (E : Nat → Bool) : Nat :=
  coordSum n (fun i => if E i then w i else 0)

/-- Unnormalised mass of an event on outcome vectors under a product law. -/
def jointEventMass (sel : WeightPair → Nat → Nat) (ps : List WeightPair)
    (E : List Nat → Bool) : Nat :=
  jointSum ps (fun v => if E v then jointWeight sel ps v else 0)

theorem coordL1_eq (p : WeightPair) :
    coordL1 p = coordSum p.size (fun i =>
      Spec.natAbsDiff (p.impl i * coordSum p.size p.ideal)
        (p.ideal i * coordSum p.size p.impl)) := by rfl

theorem coordL1_mk (n : Nat) (a b : Nat → Nat) :
    coordL1 ⟨n, a, b⟩ = coordSum n (fun i =>
      Spec.natAbsDiff (a i * coordSum n b) (b i * coordSum n a)) := by rfl

theorem jointL1_eq (ps : List WeightPair) :
    jointL1 ps = jointSum ps (fun v =>
      Spec.natAbsDiff (jointWeight WeightPair.impl ps v * jointTotal WeightPair.ideal ps)
        (jointWeight WeightPair.ideal ps v * jointTotal WeightPair.impl ps)) := by rfl

theorem coordEventMass_eq (n : Nat) (w : Nat → Nat) (E : Nat → Bool) :
    coordEventMass n w E = coordSum n (fun i => if E i then w i else 0) := by rfl

theorem jointEventMass_eq (sel : WeightPair → Nat → Nat) (ps : List WeightPair)
    (E : List Nat → Bool) :
    jointEventMass sel ps E = jointSum ps (fun v => if E v then jointWeight sel ps v else 0) := by
  rfl

theorem jointSum_isFinSum : ∀ ps : List WeightPair, IsFinSum (jointSum ps)
  | [] => ⟨fun _ _ => by rfl, fun _ _ h => h []⟩
  | p :: ps =>
    (sampleSum_isFinSum p.size).nest (jointSum_isFinSum ps)
      (fun (x : Fin p.size) (v : List Nat) => x.val :: v)

/-- The product weights sum to the product of the totals. -/
theorem jointSum_jointWeight (sel : WeightPair → Nat → Nat) :
    ∀ ps : List WeightPair, jointSum ps (jointWeight sel ps) = jointTotal sel ps
  | [] => by rfl
  | p :: ps => by
    have hInner : ∀ x : Fin p.size,
        jointSum ps (fun v => sel p x.val * jointWeight sel ps v) =
          sel p x.val * jointTotal sel ps :=
      fun x => ((jointSum_isFinSum ps).mul_left (sel p x.val) (jointWeight sel ps)).trans
        (congrArg (fun t => sel p x.val * t) (jointSum_jointWeight sel ps))
    show Spec.sampleSum p.size
        (fun x => jointSum ps (fun v => sel p x.val * jointWeight sel ps v)) =
      coordSum p.size (sel p) * jointTotal sel ps
    rw [sampleSum_congr hInner]
    exact (sampleSum_isFinSum p.size).mul_right (fun x => sel p x.val) (jointTotal sel ps)

theorem jointTotal_pos (sel : WeightPair → Nat → Nat) :
    ∀ ps : List WeightPair, (∀ p, p ∈ ps → 0 < coordSum p.size (sel p)) →
      0 < jointTotal sel ps
  | [], _ => Nat.one_pos
  | p :: ps, h =>
    Nat.mul_pos (h p (List.mem_cons.mpr (Or.inl rfl)))
      (jointTotal_pos sel ps (fun q hq => h q (List.mem_cons.mpr (Or.inr hq))))

/-- One step of the product bound: adding a coordinate adds its distance. -/
theorem jointL1_cons_le (p : WeightPair) (ps : List WeightPair) :
    jointL1 (p :: ps) ≤
      coordL1 p * (jointTotal WeightPair.impl ps * jointTotal WeightPair.ideal ps) +
        coordSum p.size p.impl * coordSum p.size p.ideal * jointL1 ps := by
  have h := (sampleSum_isFinSum p.size).cross_l1_prod_le (jointSum_isFinSum ps)
    (fun x : Fin p.size => p.impl x.val) (fun x : Fin p.size => p.ideal x.val)
    (jointWeight WeightPair.impl ps) (jointWeight WeightPair.ideal ps)
  rw [jointSum_jointWeight, jointSum_jointWeight] at h
  exact h

private theorem joint_step_arith (J l J' A B A' B' e d m : Nat)
    (hc : J ≤ l * (A' * B') + A * B * J') (hp : l * d ≤ e * (A * B))
    (ih : J' * d ≤ m * e * (A' * B')) :
    J * d ≤ (m + 1) * e * (A * A' * (B * B')) :=
  calc J * d ≤ (l * (A' * B') + A * B * J') * d := Nat.mul_le_mul_right d hc
    _ = l * d * (A' * B') + A * B * (J' * d) := by
        rw [Nat.add_mul]
        congr 1 <;> ac_rfl
    _ ≤ e * (A * B) * (A' * B') + A * B * (m * e * (A' * B')) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hp) (Nat.mul_le_mul_left _ ih)
    _ = (m + 1) * e * (A * A' * (B * B')) := by
        have e1 : e * (A * B) * (A' * B') = e * (A * A' * (B * B')) := by ac_rfl
        have e2 : A * B * (m * e * (A' * B')) = m * (e * (A * A' * (B * B'))) := by ac_rfl
        rw [e1, e2, Nat.mul_assoc (m + 1), Nat.succ_mul]
        exact Nat.add_comm _ _

/-- **Product bound for a list of coordinates.** If every coordinate has
    `TV ≤ e / (2 * d)` (cross-multiplied: `coordL1 p * d ≤ e * (A_p * B_p)`), then the two
    product laws have `TV ≤ m * e / (2 * d)` for `m` coordinates. -/
theorem jointL1_mul_le (e d : Nat) :
    ∀ ps : List WeightPair,
      (∀ p, p ∈ ps → coordL1 p * d ≤ e * (coordSum p.size p.impl * coordSum p.size p.ideal)) →
      jointL1 ps * d ≤
        ps.length * e * (jointTotal WeightPair.impl ps * jointTotal WeightPair.ideal ps)
  | [], _ => by
    show Spec.natAbsDiff (1 * 1) (1 * 1) * d ≤ 0 * e * (1 * 1)
    have h0 : Spec.natAbsDiff (1 * 1) (1 * 1) = 0 := by decide
    rw [h0, Nat.zero_mul]
    exact Nat.zero_le _
  | p :: ps, h =>
    joint_step_arith _ _ _ _ _ _ _ e d ps.length (jointL1_cons_le p ps)
      (h p (List.mem_cons.mpr (Or.inl rfl)))
      (jointL1_mul_le e d ps (fun q hq => h q (List.mem_cons.mpr (Or.inr hq))))

/-- Event probabilities transfer on one coordinate:
    `2 * |impl(E) * B - ideal(E) * A| ≤ coordL1`. -/
theorem coordEvent_cross_le (p : WeightPair) (E : Nat → Bool) :
    2 * Spec.natAbsDiff (coordEventMass p.size p.impl E * coordSum p.size p.ideal)
        (coordEventMass p.size p.ideal E * coordSum p.size p.impl) ≤ coordL1 p :=
  (sampleSum_isFinSum p.size).event_cross_le (fun x : Fin p.size => p.impl x.val)
    (fun x : Fin p.size => p.ideal x.val) (fun x : Fin p.size => E x.val)

/-- Event probabilities transfer on outcome vectors:
    `2 * |impl(E) * ∏B - ideal(E) * ∏A| ≤ jointL1`. -/
theorem jointEvent_cross_le (ps : List WeightPair) (E : List Nat → Bool) :
    2 * Spec.natAbsDiff
        (jointEventMass WeightPair.impl ps E * jointTotal WeightPair.ideal ps)
        (jointEventMass WeightPair.ideal ps E * jointTotal WeightPair.impl ps) ≤ jointL1 ps := by
  have h := (jointSum_isFinSum ps).event_cross_le (jointWeight WeightPair.impl ps)
    (jointWeight WeightPair.ideal ps) E
  rw [jointSum_jointWeight, jointSum_jointWeight] at h
  exact h

/-! ## 5. The Gaussian box coordinate -/

/-- Acceptance threshold of `sample_gaussian_box` for proposal index `i`, i.e. for the signed
    proposal `x = i - half` with exponent `x * x`. -/
@[expose] def gaussianBoxWeight (half i : Nat) : Nat :=
  gaussianExpProbability 24 (Spec.natAbsDiff i half * Spec.natAbsDiff i half)

/-- The box coordinate with `2 * half` proposals, the production thresholds as `impl` weights
    and a given `ideal` weight vector. -/
def gaussianBoxPair (half : Nat) (ideal : Nat → Nat) : WeightPair :=
  ⟨2 * half, gaussianBoxWeight half, ideal⟩

theorem gaussianBoxPair_eq (half : Nat) (ideal : Nat → Nat) :
    gaussianBoxPair half ideal = ⟨2 * half, gaussianBoxWeight half, ideal⟩ := by rfl

/-- `ideal` is, after one common positive rational rescaling `D / c`, pointwise between the
    production threshold and the production threshold plus 49 units of `2^-192`. -/
def GaussianIdealBracket (half : Nat) (ideal : Nat → Nat) : Prop :=
  ∃ c D : Nat, 0 < c ∧ 0 < D ∧ ∀ i, i < 2 * half →
    gaussianBoxWeight half i * D ≤ c * ideal i ∧
      c * ideal i ≤ (gaussianBoxWeight half i + 49) * D

theorem gaussianIdealBracket_iff (half : Nat) (ideal : Nat → Nat) :
    GaussianIdealBracket half ideal ↔
      ∃ c D : Nat, 0 < c ∧ 0 < D ∧ ∀ i, i < 2 * half →
        gaussianBoxWeight half i * D ≤ c * ideal i ∧
          c * ideal i ≤ (gaussianBoxWeight half i + 49) * D := by
  exact Iff.rfl

/-- Exact total of the production thresholds over the response box `[-3070, 3070)`. -/
theorem gaussianBoxTotal_3070 :
    coordSum 6140 (gaussianBoxWeight 3070) =
      11013925155604111574515082536301237377902248349108807478188184 :=
  (coordSum_eq_weightPrefixSum (gaussianBoxWeight 3070) 6140).trans (by decide +kernel)

/-- Exact total of the production thresholds over the mask box `[-3072, 3072)`. -/
theorem gaussianBoxTotal_3072 :
    coordSum 6144 (gaussianBoxWeight 3072) =
      11013926816664343041883888503581869188773652656392113139093142 :=
  (coordSum_eq_weightPrefixSum (gaussianBoxWeight 3072) 6144).trans (by decide +kernel)

theorem gaussianBoxTotal_lower (half : Nat) (hHalf : half = 3070 ∨ half = 3072) :
    1754 * 2 ^ 192 ≤ coordSum (2 * half) (gaussianBoxWeight half) := by
  rcases hHalf with h | h
  · subst h
    show 1754 * 2 ^ 192 ≤ coordSum 6140 (gaussianBoxWeight 3070)
    rw [gaussianBoxTotal_3070]
    decide +kernel
  · subst h
    show 1754 * 2 ^ 192 ≤ coordSum 6144 (gaussianBoxWeight 3072)
    rw [gaussianBoxTotal_3072]
    decide +kernel

theorem gaussianBox_idealTotal_pos (half : Nat) (hHalf : half = 3070 ∨ half = 3072)
    (ideal : Nat → Nat) (hB : GaussianIdealBracket half ideal) :
    0 < coordSum (2 * half) ideal := by
  obtain ⟨c, D, _, hD, h⟩ := hB
  have hT : coordSum (2 * half) (gaussianBoxWeight half) * D ≤ c * coordSum (2 * half) ideal :=
    (sampleSum_isFinSum (2 * half)).total_le_of_bracket
      (fun x : Fin (2 * half) => gaussianBoxWeight half x.val) (fun x => ideal x.val) c D
      (fun x => (h x.val x.isLt).1)
  have hA := gaussianBoxTotal_lower half hHalf
  have hApos : 0 < coordSum (2 * half) (gaussianBoxWeight half) :=
    Nat.lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.two_pow_pos 192)) hA
  have hAD := Nat.mul_pos hApos hD
  by_cases h0 : coordSum (2 * half) ideal = 0
  · rw [h0, Nat.mul_zero] at hT
    omega
  · exact Nat.pos_of_ne_zero h0

/-- One coordinate, any `half`: `∑ |impl i * B - ideal i * A| ≤ 2 * (n * 49) * B` with
    `n = 2 * half` proposals, i.e. `TV ≤ n * 49 / A`. -/
theorem gaussianBox_coordL1_le (half : Nat) (ideal : Nat → Nat)
    (hB : GaussianIdealBracket half ideal) :
    coordL1 (gaussianBoxPair half ideal) ≤ 2 * (2 * half * 49) * coordSum (2 * half) ideal := by
  obtain ⟨c, D, hc, _, h⟩ := hB
  have hL := (sampleSum_isFinSum (2 * half)).cross_l1_le_of_bracket
    (fun x : Fin (2 * half) => gaussianBoxWeight half x.val) (fun x => ideal x.val) c D 49 hc
    (fun x => (h x.val x.isLt).1) (fun x => (h x.val x.isLt).2)
  have hOne : Spec.sampleSum (2 * half) (fun _ => 1) = 2 * half := coordSum_one (2 * half)
  rw [hOne] at hL
  exact hL

private theorem tv_bits_arith {L n B A K d : Nat} (hL : L ≤ 2 * n * B) (hn : n * K < d)
    (hA : d ≤ A) (hB : 0 < B) : L * K < 2 * (A * B) := by
  have h1 : L * K ≤ 2 * n * B * K := Nat.mul_le_mul_right _ hL
  have h2 : 2 * n * B * K = 2 * (n * K * B) := by ac_rfl
  have h3 : n * K * B < A * B := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_lt_of_le hn hA) hB
  omega

private theorem half_lt_of_two_mul {x l w k : Nat} (hE : 2 * x ≤ l) (hTv : l * k < 2 * w) :
    x * k < w := by
  have h := Nat.mul_le_mul_right k hE
  rw [Nat.mul_assoc] at h
  omega

/-- **Per-coordinate total-variation bound.** For the response box (`half = 3070`) and the
    mask box (`half = 3072`), and every ideal weight vector inside the 49-unit bracket, the
    law `impl / A` of an accepted proposal and the law `ideal / B` satisfy
    `coordL1 / (2 * A * B) < 2^-184`. -/
theorem q192_gaussian_coordinate_tvd_bound (half : Nat) (hHalf : half = 3070 ∨ half = 3072)
    (ideal : Nat → Nat) (hB : GaussianIdealBracket half ideal) :
    coordL1 (gaussianBoxPair half ideal) * 2 ^ 184 <
      2 * (coordSum (2 * half) (gaussianBoxWeight half) * coordSum (2 * half) ideal) := by
  have hL := gaussianBox_coordL1_le half ideal hB
  have hA := gaussianBoxTotal_lower half hHalf
  have hBpos := gaussianBox_idealTotal_pos half hHalf ideal hB
  have hn : 2 * half * 49 * 2 ^ 184 < 1754 * 2 ^ 192 := by
    rcases hHalf with h | h <;> subst h <;> decide
  exact tv_bits_arith hL hn hA hBpos

/-- Per-coordinate event transfer: for every event on the proposals,
    `|P_impl(E) - P_ideal(E)| < 2^-184`. -/
theorem q192_gaussian_coordinate_event_transfer (half : Nat)
    (hHalf : half = 3070 ∨ half = 3072) (ideal : Nat → Nat)
    (hB : GaussianIdealBracket half ideal) (E : Nat → Bool) :
    Spec.natAbsDiff
        (coordEventMass (2 * half) (gaussianBoxWeight half) E * coordSum (2 * half) ideal)
        (coordEventMass (2 * half) ideal E * coordSum (2 * half) (gaussianBoxWeight half)) *
        2 ^ 184 <
      coordSum (2 * half) (gaussianBoxWeight half) * coordSum (2 * half) ideal := by
  have hTv := q192_gaussian_coordinate_tvd_bound half hHalf ideal hB
  have hE : 2 * Spec.natAbsDiff
      (coordEventMass (2 * half) (gaussianBoxWeight half) E * coordSum (2 * half) ideal)
      (coordEventMass (2 * half) ideal E * coordSum (2 * half) (gaussianBoxWeight half)) ≤
      coordL1 (gaussianBoxPair half ideal) := coordEvent_cross_le (gaussianBoxPair half ideal) E
  exact half_lt_of_two_mul hE hTv

/-- A batch of box coordinates: each entry is `(half, ideal)`. -/
def gaussianBatch (cs : List (Nat × (Nat → Nat))) : List WeightPair :=
  cs.map (fun c => gaussianBoxPair c.1 c.2)

theorem gaussianBatch_eq (cs : List (Nat × (Nat → Nat))) :
    gaussianBatch cs = cs.map (fun c => gaussianBoxPair c.1 c.2) := by rfl

/-- **Batch bound, any number of coordinates.** With `m` box coordinates (response or mask),
    each with its own ideal weights inside the bracket, the product laws satisfy
    `TV ≤ m * 6144 * 49 / (1754 * 2^192)`. -/
theorem gaussianBatch_jointL1_le (cs : List (Nat × (Nat → Nat)))
    (hCs : ∀ c, c ∈ cs → (c.1 = 3070 ∨ c.1 = 3072) ∧ GaussianIdealBracket c.1 c.2) :
    jointL1 (gaussianBatch cs) * (1754 * 2 ^ 192) ≤
      cs.length * (2 * (6144 * 49)) *
        (jointTotal WeightPair.impl (gaussianBatch cs) *
          jointTotal WeightPair.ideal (gaussianBatch cs)) := by
  have hCoord : ∀ p, p ∈ gaussianBatch cs →
      coordL1 p * (1754 * 2 ^ 192) ≤
        2 * (6144 * 49) * (coordSum p.size p.impl * coordSum p.size p.ideal) := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hHalf, hB⟩ := hCs c hc
    have hL := gaussianBox_coordL1_le c.1 c.2 hB
    have hA := gaussianBoxTotal_lower c.1 hHalf
    have hn : 2 * (2 * c.1 * 49) ≤ 2 * (6144 * 49) := by omega
    show coordL1 (gaussianBoxPair c.1 c.2) * (1754 * 2 ^ 192) ≤
      2 * (6144 * 49) * (coordSum (2 * c.1) (gaussianBoxWeight c.1) * coordSum (2 * c.1) c.2)
    calc coordL1 (gaussianBoxPair c.1 c.2) * (1754 * 2 ^ 192)
        ≤ 2 * (2 * c.1 * 49) * coordSum (2 * c.1) c.2 * (1754 * 2 ^ 192) :=
          Nat.mul_le_mul_right _ hL
      _ ≤ 2 * (6144 * 49) * coordSum (2 * c.1) c.2 *
            coordSum (2 * c.1) (gaussianBoxWeight c.1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hn) hA
      _ = 2 * (6144 * 49) *
            (coordSum (2 * c.1) (gaussianBoxWeight c.1) * coordSum (2 * c.1) c.2) := by
          rw [Nat.mul_assoc, Nat.mul_comm (coordSum (2 * c.1) c.2)]
  have h := jointL1_mul_le (2 * (6144 * 49)) (1754 * 2 ^ 192) (gaussianBatch cs) hCoord
  have hLen : (gaussianBatch cs).length = cs.length := List.length_map _
  rw [hLen] at h
  exact h

theorem gaussianBatch_totals_pos (cs : List (Nat × (Nat → Nat)))
    (hCs : ∀ c, c ∈ cs → (c.1 = 3070 ∨ c.1 = 3072) ∧ GaussianIdealBracket c.1 c.2) :
    0 < jointTotal WeightPair.impl (gaussianBatch cs) *
      jointTotal WeightPair.ideal (gaussianBatch cs) := by
  refine Nat.mul_pos (jointTotal_pos _ _ ?_) (jointTotal_pos _ _ ?_)
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact Nat.lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.two_pow_pos 192))
      (gaussianBoxTotal_lower c.1 (hCs c hc).1)
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact gaussianBox_idealTotal_pos c.1 (hCs c hc).1 c.2 (hCs c hc).2

/-- Batch bound in bits: if `m * 6144 * 49 * 2^t < 1754 * 2^192` then the product laws have
    `TV < 2^-t`. -/
theorem gaussianBatch_tvd_lt (cs : List (Nat × (Nat → Nat)))
    (hCs : ∀ c, c ∈ cs → (c.1 = 3070 ∨ c.1 = 3072) ∧ GaussianIdealBracket c.1 c.2)
    (t : Nat) (hBudget : cs.length * (6144 * 49) * 2 ^ t < 1754 * 2 ^ 192) :
    jointL1 (gaussianBatch cs) * 2 ^ t <
      2 * (jointTotal WeightPair.impl (gaussianBatch cs) *
        jointTotal WeightPair.ideal (gaussianBatch cs)) := by
  have hJ := gaussianBatch_jointL1_le cs hCs
  have hP := gaussianBatch_totals_pos cs hCs
  generalize jointL1 (gaussianBatch cs) = J at hJ ⊢
  generalize jointTotal WeightPair.impl (gaussianBatch cs) *
    jointTotal WeightPair.ideal (gaussianBatch cs) = P at hJ hP ⊢
  apply Spec.nat_lt_of_mul_lt_mul_right (k := 1754 * 2 ^ 192)
  have h1 : J * 2 ^ t * (1754 * 2 ^ 192) = J * (1754 * 2 ^ 192) * 2 ^ t := by ac_rfl
  have h2 : J * (1754 * 2 ^ 192) * 2 ^ t ≤ cs.length * (2 * (6144 * 49)) * P * 2 ^ t :=
    Nat.mul_le_mul_right _ hJ
  have h3 : cs.length * (2 * (6144 * 49)) * P * 2 ^ t =
      2 * (cs.length * (6144 * 49) * 2 ^ t * P) := by ac_rfl
  have h4 : cs.length * (6144 * 49) * 2 ^ t * P < 1754 * 2 ^ 192 * P :=
    Nat.mul_lt_mul_of_pos_right hBudget hP
  have h5 : 2 * P * (1754 * 2 ^ 192) = 2 * (1754 * 2 ^ 192 * P) := by ac_rfl
  omega

/-- **Batch total-variation bound for the RLWE proof.** For at most
    `49152 = 24 * 2 * 1024` box coordinates, each response or mask, and any ideal weights
    inside the brackets, the joint law of the accepted proposals and the product of the
    ideal laws satisfy `jointL1 / (2 * ∏A * ∏B) < 2^-168`. -/
theorem q192_rlwe_batch_tvd_bound (cs : List (Nat × (Nat → Nat)))
    (hLen : cs.length ≤ 49152)
    (hCs : ∀ c, c ∈ cs → (c.1 = 3070 ∨ c.1 = 3072) ∧ GaussianIdealBracket c.1 c.2) :
    jointL1 (gaussianBatch cs) * 2 ^ 168 <
      2 * (jointTotal WeightPair.impl (gaussianBatch cs) *
        jointTotal WeightPair.ideal (gaussianBatch cs)) :=
  gaussianBatch_tvd_lt cs hCs 168 (by omega)

/-- The same bound for at most `24576 = 24 * 1024` coordinates (one polynomial across the 24
    repetitions): `TV < 2^-169`. -/
theorem q192_rlwe_poly_batch_tvd_bound (cs : List (Nat × (Nat → Nat)))
    (hLen : cs.length ≤ 24576)
    (hCs : ∀ c, c ∈ cs → (c.1 = 3070 ∨ c.1 = 3072) ∧ GaussianIdealBracket c.1 c.2) :
    jointL1 (gaussianBatch cs) * 2 ^ 169 <
      2 * (jointTotal WeightPair.impl (gaussianBatch cs) *
        jointTotal WeightPair.ideal (gaussianBatch cs)) :=
  gaussianBatch_tvd_lt cs hCs 169 (by omega)

/-- Batch event transfer in bits: under the budget of `gaussianBatch_tvd_lt`, every event on
    outcome vectors has `|P_impl(E) - P_ideal(E)| < 2^-t`. -/
theorem gaussianBatch_event_transfer (cs : List (Nat × (Nat → Nat)))
    (hCs : ∀ c, c ∈ cs → (c.1 = 3070 ∨ c.1 = 3072) ∧ GaussianIdealBracket c.1 c.2)
    (t : Nat) (hBudget : cs.length * (6144 * 49) * 2 ^ t < 1754 * 2 ^ 192)
    (E : List Nat → Bool) :
    Spec.natAbsDiff
        (jointEventMass WeightPair.impl (gaussianBatch cs) E *
          jointTotal WeightPair.ideal (gaussianBatch cs))
        (jointEventMass WeightPair.ideal (gaussianBatch cs) E *
          jointTotal WeightPair.impl (gaussianBatch cs)) * 2 ^ t <
      jointTotal WeightPair.impl (gaussianBatch cs) *
        jointTotal WeightPair.ideal (gaussianBatch cs) := by
  have hTv := gaussianBatch_tvd_lt cs hCs t hBudget
  exact half_lt_of_two_mul (jointEvent_cross_le (gaussianBatch cs) E) hTv

/-- Event transfer for the full batch of at most 49152 coordinates:
    `|P_impl(E) - P_ideal(E)| < 2^-168` for every event `E`. -/
theorem q192_rlwe_batch_event_transfer (cs : List (Nat × (Nat → Nat)))
    (hLen : cs.length ≤ 49152)
    (hCs : ∀ c, c ∈ cs → (c.1 = 3070 ∨ c.1 = 3072) ∧ GaussianIdealBracket c.1 c.2)
    (E : List Nat → Bool) :
    Spec.natAbsDiff
        (jointEventMass WeightPair.impl (gaussianBatch cs) E *
          jointTotal WeightPair.ideal (gaussianBatch cs))
        (jointEventMass WeightPair.ideal (gaussianBatch cs) E *
          jointTotal WeightPair.impl (gaussianBatch cs)) * 2 ^ 168 <
      jointTotal WeightPair.impl (gaussianBatch cs) *
        jointTotal WeightPair.ideal (gaussianBatch cs) :=
  gaussianBatch_event_transfer cs hCs 168 (by omega) E

/-- Squared Euclidean norm of the signed vector `(i - half)_i` of an index vector. -/
def centeredSqNorm (half : Nat) : List Nat → Nat
  | [] => 0
  | i :: v => Spec.natAbsDiff i half * Spec.natAbsDiff i half + centeredSqNorm half v

theorem centeredSqNorm_nil (half : Nat) : centeredSqNorm half [] = 0 := by rfl

theorem centeredSqNorm_cons (half i : Nat) (v : List Nat) :
    centeredSqNorm half (i :: v) =
      Spec.natAbsDiff i half * Spec.natAbsDiff i half + centeredSqNorm half v := by rfl

/-- **Tail event of one `(z_s, z_e)` pair.** For 2048 box coordinates of one kind, the event
    `‖z‖_2^2 > 1_500_000_000` (`RLWE_ZKPOK_PAIR_L2_SQ_BOUND`) has probabilities under the
    production law and under any bracketed ideal product law that differ by less than
    `2^-173`. The probability itself is not computed here. -/
theorem q192_rlwe_pair_l2_tail_transfer (half : Nat) (hHalf : half = 3070 ∨ half = 3072)
    (cs : List (Nat × (Nat → Nat))) (hLen : cs.length = 2048)
    (hCs : ∀ c, c ∈ cs → c.1 = half ∧ GaussianIdealBracket half c.2) :
    Spec.natAbsDiff
        (jointEventMass WeightPair.impl (gaussianBatch cs)
            (fun v => decide (1500000000 < centeredSqNorm half v)) *
          jointTotal WeightPair.ideal (gaussianBatch cs))
        (jointEventMass WeightPair.ideal (gaussianBatch cs)
            (fun v => decide (1500000000 < centeredSqNorm half v)) *
          jointTotal WeightPair.impl (gaussianBatch cs)) * 2 ^ 173 <
      jointTotal WeightPair.impl (gaussianBatch cs) *
        jointTotal WeightPair.ideal (gaussianBatch cs) :=
  gaussianBatch_event_transfer cs
    (fun c hc => ⟨(hCs c hc).1 ▸ hHalf, (hCs c hc).1 ▸ (hCs c hc).2⟩) 173 (by omega) _

/-! ## 6. One trial of the box sampler -/

/-- One trial of `sample_gaussian_box`: `r` is the 13-bit proposal draw and `u` the 192-bit
    coin. The draw is valid iff `r < 2 * half`; a valid draw proposes `x = r - half`, which is
    accepted iff `u` is below the threshold for the exponent `x * x`. The result is the
    accepted value, or `none` when the sampler draws again. -/
@[expose] def gaussianBoxTrial (half : Nat) (r : Fin 8192) (u : Fin (2 ^ 192)) : Option Int :=
  if r.val < 2 * half ∧ u.val < gaussianBoxWeight half r.val then
    some ((r.val : Int) - (half : Int))
  else none

/-- Every accepted value lies in the box `[-half, half)`. -/
theorem gaussianBoxTrial_range (half : Nat) (r : Fin 8192) (u : Fin (2 ^ 192)) (x : Int)
    (h : gaussianBoxTrial half r u = some x) : -(half : Int) ≤ x ∧ x < (half : Int) := by
  by_cases hc : r.val < 2 * half ∧ u.val < gaussianBoxWeight half r.val
  · have hT : gaussianBoxTrial half r u = some ((r.val : Int) - (half : Int)) := by
      unfold gaussianBoxTrial
      exact ite_eq_left hc
    rw [hT] at h
    have hx : (r.val : Int) - (half : Int) = x := Option.some.inj h
    have hr := hc.1
    exact ⟨by omega, by omega⟩
  · have hT : gaussianBoxTrial half r u = none := by
      unfold gaussianBoxTrial
      exact ite_eq_right hc
    rw [hT] at h
    cases h

/-- Every accepted response coordinate lies in `[-3070, 3069]`, so the verifier's bound
    `RLWE_ZKPOK_Z_BOUND = 3070` on `|z|_∞` holds for every coin sequence. -/
theorem gaussianBoxTrial_response_inf_bound (r : Fin 8192) (u : Fin (2 ^ 192)) (x : Int)
    (h : gaussianBoxTrial 3070 r u = some x) : -3070 ≤ x ∧ x ≤ 3069 ∧ x.natAbs ≤ 3070 := by
  have h' := gaussianBoxTrial_range 3070 r u x h
  exact ⟨by omega, by omega, by omega⟩

/-- **Output count of one trial.** Among the `8192 * 2^192` coin pairs `(r, u)`, exactly
    `gaussianBoxWeight half i` produce the value `i - half`. Hence, conditioned on acceptance,
    a trial outputs `i - half` with probability `gaussianBoxWeight half i / A`, the `impl` law
    of `gaussianBoxPair`. -/
theorem gaussianBoxTrial_output_count (half i : Nat) (hi : i < 2 * half)
    (hHalf : 2 * half ≤ 8192) :
    Spec.sampleSum 8192 (fun r : Fin 8192 =>
      Spec.sampleSum (2 ^ 192) (fun u : Fin (2 ^ 192) =>
        if gaussianBoxTrial half r u = some ((i : Int) - (half : Int)) then 1 else 0)) =
      gaussianBoxWeight half i := by
  have hW : gaussianBoxWeight half i ≤ 2 ^ 192 := gaussianExpProbability_le 24 (by decide) _
  have hInner : ∀ r : Fin 8192,
      Spec.sampleSum (2 ^ 192) (fun u : Fin (2 ^ 192) =>
        if gaussianBoxTrial half r u = some ((i : Int) - (half : Int)) then 1 else 0) =
        (if r.val = i then gaussianBoxWeight half i else 0) := by
    intro r
    by_cases hr : r.val = i
    · rw [ite_eq_left hr]
      refine (sampleSum_congr (fun u => ?_)).trans
        (q192_accepting_coin_count (gaussianBoxWeight half i) hW)
      by_cases hu : u.val < gaussianBoxWeight half i
      · have hc : r.val < 2 * half ∧ u.val < gaussianBoxWeight half r.val :=
          ⟨by omega, by rw [hr]; exact hu⟩
        have hT : gaussianBoxTrial half r u = some ((i : Int) - (half : Int)) := by
          unfold gaussianBoxTrial
          rw [ite_eq_left hc, hr]
        rw [ite_eq_left hT, ite_eq_left hu]
      · have hnc : ¬ (r.val < 2 * half ∧ u.val < gaussianBoxWeight half r.val) :=
          fun hc => hu (by rw [← hr]; exact hc.2)
        have hT : ¬ gaussianBoxTrial half r u = some ((i : Int) - (half : Int)) := by
          unfold gaussianBoxTrial
          rw [ite_eq_right hnc]
          intro h
          cases h
        rw [ite_eq_right hT, ite_eq_right hu]
    · rw [ite_eq_right hr]
      have hZero : ∀ u : Fin (2 ^ 192),
          (if gaussianBoxTrial half r u = some ((i : Int) - (half : Int)) then 1 else 0) = 0 := by
        intro u
        refine ite_eq_right (fun hT => hr ?_)
        unfold gaussianBoxTrial at hT
        split at hT
        · have hx := Option.some.inj hT
          omega
        · cases hT
      rw [sampleSum_congr hZero]
      exact (sampleSum_isFinSum (2 ^ 192)).zero
  rw [sampleSum_congr hInner]
  have h := coordSum_point_indicator i (gaussianBoxWeight half i) 8192
  rw [ite_eq_left (by omega : i < 8192)] at h
  exact h

/-- **Acceptance count of one trial.** Exactly `A = ∑_i gaussianBoxWeight half i` of the
    `8192 * 2^192` coin pairs are accepted. -/
theorem gaussianBoxTrial_accept_count (half : Nat) (hHalf : 2 * half ≤ 8192) :
    Spec.sampleSum 8192 (fun r : Fin 8192 =>
      Spec.sampleSum (2 ^ 192) (fun u : Fin (2 ^ 192) =>
        if (gaussianBoxTrial half r u).isSome then 1 else 0)) =
      coordSum (2 * half) (gaussianBoxWeight half) := by
  have hInner : ∀ r : Fin 8192,
      Spec.sampleSum (2 ^ 192) (fun u : Fin (2 ^ 192) =>
        if (gaussianBoxTrial half r u).isSome then 1 else 0) =
        (if r.val < 2 * half then gaussianBoxWeight half r.val else 0) := by
    intro r
    have hW : gaussianBoxWeight half r.val ≤ 2 ^ 192 :=
      gaussianExpProbability_le 24 (by decide) _
    by_cases hr : r.val < 2 * half
    · rw [ite_eq_left hr]
      refine (sampleSum_congr (fun u => ?_)).trans
        (q192_accepting_coin_count (gaussianBoxWeight half r.val) hW)
      by_cases hu : u.val < gaussianBoxWeight half r.val
      · have hT : gaussianBoxTrial half r u = some ((r.val : Int) - (half : Int)) := by
          unfold gaussianBoxTrial
          exact ite_eq_left ⟨hr, hu⟩
        rw [hT, ite_eq_left hu]
        rfl
      · have hT : gaussianBoxTrial half r u = none := by
          unfold gaussianBoxTrial
          exact ite_eq_right (fun hc => hu hc.2)
        rw [hT, ite_eq_right hu]
        rfl
    · rw [ite_eq_right hr]
      have hZero : ∀ u : Fin (2 ^ 192),
          (if (gaussianBoxTrial half r u).isSome then 1 else 0) = 0 := by
        intro u
        have hT : gaussianBoxTrial half r u = none := by
          unfold gaussianBoxTrial
          exact ite_eq_right (fun hc => hr hc.1)
        rw [hT]
        rfl
      rw [sampleSum_congr hZero]
      exact (sampleSum_isFinSum (2 ^ 192)).zero
  rw [sampleSum_congr hInner]
  exact coordSum_truncate (2 * half) (gaussianBoxWeight half) 8192 hHalf

/-! ## 7. Eight-bit truncation violates the bounds -/

/-- **Truncation witness.** Replace the Q192 comparison by an 8-bit one: threshold
    `⌊p / 2^184⌋`, coin uniform on `2^8` values. At exponent `e = 1`
    (a) its acceptance probability is more than `2^-128` below that of the Q192 comparison, and
    (b) it is more than `2^-128` below the ideal probability of every factor vector inside the
    table bracket, so the 49-unit bound of
    `q192_sampler_pointwise_error_le_pow2_neg192` fails for it. -/
theorem tooth_q8_truncation_violates_2pow_neg128_floor :
    ∃ e : Nat, e < 2 ^ 24 ∧
      (thresholdGame (2 ^ 8) (Nat.two_pow_pos 8) (gaussianExpProbability 24 e / 2 ^ 184)).winCount *
          2 ^ 184 + 2 ^ 64 <
        (q192BernoulliGame (gaussianExpProbability 24 e)).winCount ∧
      ∀ f : Nat → Nat,
        (∀ i, i < 24 → gaussianExpPower i ≤ f i ∧ f i ≤ gaussianExpPower i + 1) →
        ((thresholdGame (2 ^ 8) (Nat.two_pow_pos 8)
              (gaussianExpProbability 24 e / 2 ^ 184)).winCount * 2 ^ 184 + 2 ^ 64) *
            (2 ^ 192) ^ bitCount e 24 <
          2 ^ 192 * bitSelProd f (fun _ => 1) e 24 := by
  have ha : (thresholdGame (2 ^ 8) (Nat.two_pow_pos 8)
        (gaussianExpProbability 24 1 / 2 ^ 184)).winCount * 2 ^ 184 + 2 ^ 64 <
      (q192BernoulliGame (gaussianExpProbability 24 1)).winCount := by
    rw [thresholdGame_winCount,
      q192BernoulliGame_winCount _ (gaussianExpProbability_le 24 (by decide) 1)]
    decide +kernel
  refine ⟨1, by decide, ha, fun f hf => ?_⟩
  exact Nat.lt_of_lt_of_le
    (Nat.mul_lt_mul_of_pos_right ha (Nat.pow_pos (Nat.two_pow_pos 192)))
    (q192_sampler_pointwise_error_le_pow2_neg192 1 f hf).1

#tooth_pair Qsag.q192_sampler_pointwise_error_le_pow2_neg192 vs
  Qsag.tooth_q8_truncation_violates_2pow_neg128_floor

/-- **Truncation witness for the coordinate law.** The Q192 thresholds are themselves an ideal
    weight vector inside the bracket, and the response-box law built from the 8-bit truncated
    thresholds `⌊p / 2^184⌋` is at total-variation distance more than `2^-9` from it. The
    bound `2^-184` of `q192_gaussian_coordinate_tvd_bound` therefore fails for the truncated
    sampler by a wide margin, in particular at the `2^-128` level. -/
theorem tooth_q8_truncation_coordinate_tvd_exceeds_2pow_neg9 :
    ∃ ideal : Nat → Nat, GaussianIdealBracket 3070 ideal ∧
      2 * (coordSum 6140 (fun i => gaussianBoxWeight 3070 i / 2 ^ 184) * coordSum 6140 ideal) <
        coordL1 ⟨6140, fun i => gaussianBoxWeight 3070 i / 2 ^ 184, ideal⟩ * 2 ^ 9 := by
  refine ⟨gaussianBoxWeight 3070, ⟨1, 1, by decide, by decide, fun i _ => ⟨by omega, by omega⟩⟩, ?_⟩
  have hA := gaussianBoxTotal_3070
  have hA8 : coordSum 6140 (fun i => gaussianBoxWeight 3070 i / 2 ^ 184) = 446449 :=
    (coordSum_eq_weightPrefixSum _ 6140).trans (by decide +kernel)
  rw [coordL1_mk, hA, hA8, coordSum_eq_weightPrefixSum]
  decide +kernel

#tooth_pair Qsag.q192_gaussian_coordinate_tvd_bound vs
  Qsag.tooth_q8_truncation_coordinate_tvd_exceeds_2pow_neg9

/-! ## 8. The table against a rational enclosure of the Gaussian base -/

/-- Numerator of the alternating partial sum `∑_{j ≤ J} (-1)^j / (j! * c^j)` over the
    denominator `expNegTaylorDenom c J = J! * c^J`: `N_0 = 1`, `N_j = N_{j-1} * (j * c) ± 1`. -/
def expNegTaylorNumer (c : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 =>
    if (j + 1) % 2 = 0 then expNegTaylorNumer c j * ((j + 1) * c) + 1
    else expNegTaylorNumer c j * ((j + 1) * c) - 1

/-- `J! * c^J`. -/
def expNegTaylorDenom (c : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => expNegTaylorDenom c j * ((j + 1) * c)

theorem expNegTaylorNumer_zero (c : Nat) : expNegTaylorNumer c 0 = 1 := by rfl

theorem expNegTaylorNumer_succ (c j : Nat) :
    expNegTaylorNumer c (j + 1) =
      if (j + 1) % 2 = 0 then expNegTaylorNumer c j * ((j + 1) * c) + 1
      else expNegTaylorNumer c j * ((j + 1) * c) - 1 := by rfl

theorem expNegTaylorDenom_zero (c : Nat) : expNegTaylorDenom c 0 = 1 := by rfl

theorem expNegTaylorDenom_succ (c j : Nat) :
    expNegTaylorDenom c (j + 1) = expNegTaylorDenom c j * ((j + 1) * c) := by rfl

/-- The rational `a / b` lies between the partial sums of orders 19 and 20 of the series
    `∑ (-1)^j x^j / j!` at `x = 1/980000`. The alternating-series estimate, which is not
    formalised here, places `e^(-1/980000)` strictly inside this interval. -/
def InExpNegEnclosure (a b : Nat) : Prop :=
  0 < b ∧ expNegTaylorNumer 980000 19 * b ≤ a * expNegTaylorDenom 980000 19 ∧
    a * expNegTaylorDenom 980000 20 ≤ expNegTaylorNumer 980000 20 * b

theorem inExpNegEnclosure_iff (a b : Nat) :
    InExpNegEnclosure a b ↔
      0 < b ∧ expNegTaylorNumer 980000 19 * b ≤ a * expNegTaylorDenom 980000 19 ∧
        a * expNegTaylorDenom 980000 20 ≤ expNegTaylorNumer 980000 20 * b := by
  exact Iff.rfl

/-- The enclosure is a nonempty interval of width at most `2^-459`, and no subtraction in the
    numerator recurrence truncates. -/
theorem expNegEnclosure_nonempty_and_narrow :
    InExpNegEnclosure (expNegTaylorNumer 980000 20) (expNegTaylorDenom 980000 20) ∧
    (expNegTaylorNumer 980000 20 * expNegTaylorDenom 980000 19 -
        expNegTaylorNumer 980000 19 * expNegTaylorDenom 980000 20) * 2 ^ 459 ≤
      expNegTaylorDenom 980000 19 * expNegTaylorDenom 980000 20 ∧
    ∀ j, j < 20 → 1 ≤ expNegTaylorNumer 980000 j * ((j + 1) * 980000) :=
  ⟨⟨by decide +kernel, by decide +kernel, Nat.le_refl _⟩, by decide +kernel, by decide +kernel⟩

/-- Lower end of a fixed-point squaring chain at precision `P`: `x ↦ ⌊x^2 / P⌋`. -/
private def sqChainLo (P x0 : Nat) : Nat → Nat
  | 0 => x0
  | i + 1 => sqChainLo P x0 i ^ 2 / P

/-- Upper end of the chain: `x ↦ ⌊x^2 / P⌋ + 1`. -/
private def sqChainHi (P x0 : Nat) : Nat → Nat
  | 0 => x0
  | i + 1 => sqChainHi P x0 i ^ 2 / P + 1

private theorem div_succ_mul_gt (x m : Nat) (hm : 0 < m) : x < (x / m + 1) * m := by
  have h := Nat.lt_mul_div_succ x hm
  rw [Nat.mul_comm] at h
  exact h

private theorem sq_step (P l h A B : Nat) (hP : 0 < P) (hLo : l * B ≤ P * A)
    (hHi : P * A ≤ h * B) :
    l ^ 2 / P * B ^ 2 ≤ P * A ^ 2 ∧ P * A ^ 2 ≤ (h ^ 2 / P + 1) * B ^ 2 := by
  rw [Nat.pow_two l, Nat.pow_two h, Nat.pow_two A, Nat.pow_two B]
  have hl : l * l / P * P ≤ l * l := Nat.div_mul_le_self _ _
  have hh : h * h ≤ (h * h / P + 1) * P := Nat.le_of_lt (div_succ_mul_gt (h * h) P hP)
  generalize l * l / P = l' at hl ⊢
  generalize h * h / P = h' at hh ⊢
  refine ⟨Nat.le_of_mul_le_mul_left ?_ hP, Nat.le_of_mul_le_mul_left ?_ hP⟩
  · calc P * (l' * (B * B)) = l' * P * (B * B) := by ac_rfl
      _ ≤ l * l * (B * B) := Nat.mul_le_mul_right _ hl
      _ = l * B * (l * B) := by ac_rfl
      _ ≤ P * A * (P * A) := Nat.mul_le_mul hLo hLo
      _ = P * (P * (A * A)) := by ac_rfl
  · calc P * (P * (A * A)) = P * A * (P * A) := by ac_rfl
      _ ≤ h * B * (h * B) := Nat.mul_le_mul hHi hHi
      _ = h * h * (B * B) := by ac_rfl
      _ ≤ (h' + 1) * P * (B * B) := Nat.mul_le_mul_right _ hh
      _ = P * ((h' + 1) * (B * B)) := by ac_rfl

private theorem sqChain_bracket (P : Nat) (hP : 0 < P) (lo0 hi0 a b : Nat)
    (hLo : lo0 * b ≤ P * a) (hHi : P * a ≤ hi0 * b) :
    ∀ i : Nat, sqChainLo P lo0 i * b ^ 2 ^ i ≤ P * a ^ 2 ^ i ∧
      P * a ^ 2 ^ i ≤ sqChainHi P hi0 i * b ^ 2 ^ i
  | 0 => by
    show lo0 * b ^ 2 ^ 0 ≤ P * a ^ 2 ^ 0 ∧ P * a ^ 2 ^ 0 ≤ hi0 * b ^ 2 ^ 0
    rw [Nat.pow_zero, Nat.pow_one, Nat.pow_one]
    exact ⟨hLo, hHi⟩
  | i + 1 => by
    obtain ⟨ihLo, ihHi⟩ := sqChain_bracket P hP lo0 hi0 a b hLo hHi i
    have hpa : a ^ 2 ^ (i + 1) = (a ^ 2 ^ i) ^ 2 := by rw [Nat.pow_succ, Nat.pow_mul]
    have hpb : b ^ 2 ^ (i + 1) = (b ^ 2 ^ i) ^ 2 := by rw [Nat.pow_succ, Nat.pow_mul]
    rw [hpa, hpb]
    exact sq_step P _ _ _ _ hP ihLo ihHi

private theorem chain_base (P N19 M19 N20 M20 a b : Nat) (hM19 : 0 < M19) (hM20 : 0 < M20)
    (hLoE : N19 * b ≤ a * M19) (hHiE : a * M20 ≤ N20 * b) :
    N19 * P / M19 * b ≤ P * a ∧ P * a ≤ (N20 * P / M20 + 1) * b := by
  have hl : N19 * P / M19 * M19 ≤ N19 * P := Nat.div_mul_le_self _ _
  have hh : N20 * P ≤ (N20 * P / M20 + 1) * M20 :=
    Nat.le_of_lt (div_succ_mul_gt (N20 * P) M20 hM20)
  generalize N19 * P / M19 = l at hl ⊢
  generalize N20 * P / M20 = h at hh ⊢
  refine ⟨Nat.le_of_mul_le_mul_left ?_ hM19, Nat.le_of_mul_le_mul_left ?_ hM20⟩
  · calc M19 * (l * b) = l * M19 * b := by ac_rfl
      _ ≤ N19 * P * b := Nat.mul_le_mul_right _ hl
      _ = N19 * b * P := by ac_rfl
      _ ≤ a * M19 * P := Nat.mul_le_mul_right _ hLoE
      _ = M19 * (P * a) := by ac_rfl
  · calc M20 * (P * a) = a * M20 * P := by ac_rfl
      _ ≤ N20 * b * P := Nat.mul_le_mul_right _ hHiE
      _ = N20 * P * b := by ac_rfl
      _ ≤ (h + 1) * M20 * b := Nat.mul_le_mul_right _ hh
      _ = M20 * ((h + 1) * b) := by ac_rfl

private theorem chain_conclude (t P Q lo hi A B : Nat) (hP : 0 < P) (hB : 0 < B)
    (hcLo : lo * B ≤ P * A) (hcHi : P * A ≤ hi * B) (htLo : t * P ≤ lo * Q)
    (htHi : hi * Q < (t + 1) * P) : t * B ≤ Q * A ∧ Q * A < (t + 1) * B := by
  refine ⟨Nat.le_of_mul_le_mul_left ?_ hP, Spec.nat_lt_of_mul_lt_mul_right (k := P) ?_⟩
  · calc P * (t * B) = t * P * B := by ac_rfl
      _ ≤ lo * Q * B := Nat.mul_le_mul_right _ htLo
      _ = Q * (lo * B) := by ac_rfl
      _ ≤ Q * (P * A) := Nat.mul_le_mul_left _ hcLo
      _ = P * (Q * A) := by ac_rfl
  · calc Q * A * P = Q * (P * A) := by ac_rfl
      _ ≤ Q * (hi * B) := Nat.mul_le_mul_left _ hcHi
      _ = hi * Q * B := by ac_rfl
      _ < (t + 1) * P * B := Nat.mul_lt_mul_of_pos_right htHi hB
      _ = (t + 1) * B * P := by ac_rfl

/-- Chain start at precision `2^512`: floor of the order-19 partial sum. -/
private def expNegChainLo0 : Nat :=
  expNegTaylorNumer 980000 19 * 2 ^ 512 / expNegTaylorDenom 980000 19

/-- Chain start at precision `2^512`: floor plus one of the order-20 partial sum. -/
private def expNegChainHi0 : Nat :=
  expNegTaylorNumer 980000 20 * 2 ^ 512 / expNegTaylorDenom 980000 20 + 1

private theorem expNegChain_table_check : ∀ i, i < 30 →
    gaussianExpPower i * 2 ^ 512 ≤ sqChainLo (2 ^ 512) expNegChainLo0 i * 2 ^ 192 ∧
    sqChainHi (2 ^ 512) expNegChainHi0 i * 2 ^ 192 < (gaussianExpPower i + 1) * 2 ^ 512 := by
  decide +kernel

/-- **The table is the floor of `2^192 * q^(2^i)` for every rational `q` in the enclosure.**
    For `q = a / b` with `InExpNegEnclosure a b` and every `i < 30`:
    `table[i] ≤ 2^192 * (a / b)^(2^i) < table[i] + 1`. -/
theorem rlweGaussianExpPowers_floor_of_rational_base (a b : Nat) (hq : InExpNegEnclosure a b) :
    ∀ i, i < 30 →
      gaussianExpPower i * b ^ 2 ^ i ≤ 2 ^ 192 * a ^ 2 ^ i ∧
      2 ^ 192 * a ^ 2 ^ i < (gaussianExpPower i + 1) * b ^ 2 ^ i := by
  obtain ⟨hb, hLoE, hHiE⟩ := hq
  have hBase := chain_base (2 ^ 512) _ _ _ _ a b (by decide +kernel) (by decide +kernel)
    hLoE hHiE
  intro i hi
  obtain ⟨hcLo, hcHi⟩ := sqChain_bracket (2 ^ 512) (Nat.two_pow_pos 512) expNegChainLo0
    expNegChainHi0 a b hBase.1 hBase.2 i
  obtain ⟨htLo, htHi⟩ := expNegChain_table_check i hi
  exact chain_conclude _ _ _ _ _ _ _ (Nat.two_pow_pos 512) (Nat.pow_pos hb) hcLo hcHi htLo htHi

private theorem mod_mul_two (e m : Nat) (hm : 0 < m) :
    e % (m * 2) = e % m + m * (e / m % 2) := by
  have h1 := Nat.div_add_mod e m
  have h2 := Nat.div_add_mod (e / m) 2
  have hr := Nat.mod_lt e hm
  have hb : e / m % 2 < 2 := Nat.mod_lt _ (by decide)
  have h3 : m * (e / m) = m * 2 * (e / m / 2) + m * (e / m % 2) := by
    rw [Nat.mul_assoc m 2, ← Nat.mul_add, h2]
  have hDecomp : e = m * 2 * (e / m / 2) + (e % m + m * (e / m % 2)) := by omega
  have hLt : e % m + m * (e / m % 2) < m * 2 := by
    have h4 : m * (e / m % 2) ≤ m * 1 := Nat.mul_le_mul_left m (Nat.le_of_lt_succ hb)
    omega
  have h5 := Nat.mul_add_mod (m * 2) (e / m / 2) (e % m + m * (e / m % 2))
  rw [← hDecomp, Nat.mod_eq_of_lt hLt] at h5
  exact h5

/-- The product of `a^(2^i)` over the set bits of `e` below `bits` is `a^(e mod 2^bits)`. -/
theorem bitSelProd_pow_two_pow (a e : Nat) :
    ∀ bits : Nat, bitSelProd (fun i => a ^ 2 ^ i) (fun _ => 1) e bits = a ^ (e % 2 ^ bits)
  | 0 => by
    show 1 = a ^ (e % 2 ^ 0)
    rw [Nat.pow_zero, Nat.mod_one, Nat.pow_zero]
  | bits + 1 => by
    have hd0 : ¬ decide ((0 : Nat) = 1) = true := by decide
    have hd1 : decide ((1 : Nat) = 1) = true := by decide
    rw [bitSelProd_succ, bitSelProd_pow_two_pow a e bits, Nat.pow_succ 2 bits,
      mod_mul_two e (2 ^ bits) (Nat.two_pow_pos bits), Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ bits) with h | h
    · rw [h, ite_eq_right hd0, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    · rw [h, ite_eq_left hd1, Nat.mul_one, Nat.pow_add]

/-- **Evaluator error against the exact power `q^e`.** For every rational `q = a / b` in the
    enclosure, every `bits ≤ 30` and every exponent `e < 2^bits`, the evaluator output `p`
    satisfies `p / 2^192 ≤ q^e ≤ (p + 1 + 2 * bits) / 2^192`. -/
theorem gaussianExpProbability_rational_base (bits : Nat) (hBits : bits ≤ 30) (e : Nat)
    (he : e < 2 ^ bits) (a b : Nat) (hq : InExpNegEnclosure a b) :
    gaussianExpProbability bits e * b ^ e ≤ 2 ^ 192 * a ^ e ∧
    2 ^ 192 * a ^ e ≤ (gaussianExpProbability bits e + (1 + 2 * bits)) * b ^ e := by
  have hT := rlweGaussianExpPowers_floor_of_rational_base a b hq
  have hB := gaussianExpProbability_bracket bits hBits e (fun i => a ^ 2 ^ i)
    (fun i => b ^ 2 ^ i) (fun _ => 1)
    (fun i hi => ⟨(hT i (Nat.lt_of_lt_of_le hi hBits)).1,
      Nat.le_of_lt (hT i (Nat.lt_of_lt_of_le hi hBits)).2⟩)
  rw [bitSelProd_pow_two_pow, bitSelProd_pow_two_pow, Nat.mod_eq_of_lt he] at hB
  refine ⟨hB.1, Nat.le_trans hB.2 (Nat.mul_le_mul_right _ ?_)⟩
  have hCnt := bitCount_le e bits
  omega

/-- The production Bernoulli step against the exact power: for `e < 2^24` and every rational
    `q = a / b` in the enclosure, `Pr[accept] ≤ q^e ≤ Pr[accept] + 49 / 2^192`. -/
theorem q192_sampler_pointwise_error_rational_base (e : Nat) (he : e < 2 ^ 24) (a b : Nat)
    (hq : InExpNegEnclosure a b) :
    (q192BernoulliGame (gaussianExpProbability 24 e)).winCount * b ^ e ≤ 2 ^ 192 * a ^ e ∧
    2 ^ 192 * a ^ e ≤ ((q192BernoulliGame (gaussianExpProbability 24 e)).winCount + 49) * b ^ e := by
  rw [q192BernoulliGame_winCount _ (gaussianExpProbability_le 24 (by decide) e)]
  exact gaussianExpProbability_rational_base 24 (by decide) e he a b hq

/-- Weights of the discrete Gaussian with base `q = a / b` on the box, over the common
    denominator `b^(half^2)`: index `i` (value `x = i - half`) has weight
    `a^(x^2) * b^(half^2 - x^2)`, proportional to `q^(x^2)`. -/
def rationalGaussianWeight (a b half i : Nat) : Nat :=
  a ^ (Spec.natAbsDiff i half * Spec.natAbsDiff i half) *
    b ^ (half * half - Spec.natAbsDiff i half * Spec.natAbsDiff i half)

theorem rationalGaussianWeight_eq (a b half i : Nat) :
    rationalGaussianWeight a b half i =
      a ^ (Spec.natAbsDiff i half * Spec.natAbsDiff i half) *
        b ^ (half * half - Spec.natAbsDiff i half * Spec.natAbsDiff i half) := by rfl

/-- The discrete Gaussian with any rational base in the enclosure is inside the 49-unit
    bracket of the production thresholds. -/
theorem rationalGaussian_idealBracket (half : Nat) (hHalf : half * half < 2 ^ 24) (a b : Nat)
    (hq : InExpNegEnclosure a b) :
    GaussianIdealBracket half (rationalGaussianWeight a b half) := by
  refine ⟨2 ^ 192, b ^ (half * half), Nat.two_pow_pos 192, Nat.pow_pos hq.1, fun i hi => ?_⟩
  have hAbs : Spec.natAbsDiff i half ≤ half := by
    unfold Spec.natAbsDiff
    split <;> omega
  have he : Spec.natAbsDiff i half * Spec.natAbsDiff i half ≤ half * half :=
    Nat.mul_le_mul hAbs hAbs
  obtain ⟨h1, h2⟩ := gaussianExpProbability_rational_base 24 (by decide)
    (Spec.natAbsDiff i half * Spec.natAbsDiff i half) (Nat.lt_of_le_of_lt he hHalf) a b hq
  have hSplit : b ^ (half * half) =
      b ^ (Spec.natAbsDiff i half * Spec.natAbsDiff i half) *
        b ^ (half * half - Spec.natAbsDiff i half * Spec.natAbsDiff i half) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  show gaussianExpProbability 24 (Spec.natAbsDiff i half * Spec.natAbsDiff i half) *
        b ^ (half * half) ≤
      2 ^ 192 * (a ^ (Spec.natAbsDiff i half * Spec.natAbsDiff i half) *
        b ^ (half * half - Spec.natAbsDiff i half * Spec.natAbsDiff i half)) ∧
    2 ^ 192 * (a ^ (Spec.natAbsDiff i half * Spec.natAbsDiff i half) *
        b ^ (half * half - Spec.natAbsDiff i half * Spec.natAbsDiff i half)) ≤
      (gaussianExpProbability 24 (Spec.natAbsDiff i half * Spec.natAbsDiff i half) + 49) *
        b ^ (half * half)
  rw [hSplit, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc]
  exact ⟨Nat.mul_le_mul_right _ h1, Nat.mul_le_mul_right _ h2⟩

/-- A batch of box coordinates, one per entry of `halves`, each paired with the discrete
    Gaussian of base `a / b` on its box. -/
def rationalGaussianBatch (a b : Nat) (halves : List Nat) : List WeightPair :=
  gaussianBatch (halves.map (fun h => (h, rationalGaussianWeight a b h)))

theorem rationalGaussianBatch_eq (a b : Nat) (halves : List Nat) :
    rationalGaussianBatch a b halves =
      gaussianBatch (halves.map (fun h => (h, rationalGaussianWeight a b h))) := by rfl

private theorem rationalGaussianBatch_coords (a b : Nat) (hq : InExpNegEnclosure a b)
    (halves : List Nat) (hHalves : ∀ h, h ∈ halves → h = 3070 ∨ h = 3072) :
    ∀ c, c ∈ halves.map (fun h => (h, rationalGaussianWeight a b h)) →
      (c.1 = 3070 ∨ c.1 = 3072) ∧ GaussianIdealBracket c.1 c.2 := by
  intro c hc
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hc
  have hSq : h * h < 2 ^ 24 := by
    rcases hHalves h hh with r | r <;> subst r <;> decide
  exact ⟨hHalves h hh, rationalGaussian_idealBracket h hSq a b hq⟩

/-- **Batch bound against the discrete Gaussian with base in the enclosure.** For at most
    49152 box coordinates and every rational `q = a / b` in the enclosure, the joint law of the
    accepted proposals is at total-variation distance less than `2^-168` from the product of
    the discrete Gaussians with weights proportional to `q^(x^2)`. -/
theorem q192_rlwe_batch_tvd_bound_rational_base (a b : Nat) (hq : InExpNegEnclosure a b)
    (halves : List Nat) (hLen : halves.length ≤ 49152)
    (hHalves : ∀ h, h ∈ halves → h = 3070 ∨ h = 3072) :
    jointL1 (rationalGaussianBatch a b halves) * 2 ^ 168 <
      2 * (jointTotal WeightPair.impl (rationalGaussianBatch a b halves) *
        jointTotal WeightPair.ideal (rationalGaussianBatch a b halves)) :=
  q192_rlwe_batch_tvd_bound _ (by rw [List.length_map]; exact hLen)
    (rationalGaussianBatch_coords a b hq halves hHalves)

/-- Event transfer against the discrete Gaussian with base in the enclosure: every event on
    the outcome vectors of at most 49152 coordinates has probabilities under the two laws
    that differ by less than `2^-168`. -/
theorem q192_rlwe_batch_event_transfer_rational_base (a b : Nat) (hq : InExpNegEnclosure a b)
    (halves : List Nat) (hLen : halves.length ≤ 49152)
    (hHalves : ∀ h, h ∈ halves → h = 3070 ∨ h = 3072) (E : List Nat → Bool) :
    Spec.natAbsDiff
        (jointEventMass WeightPair.impl (rationalGaussianBatch a b halves) E *
          jointTotal WeightPair.ideal (rationalGaussianBatch a b halves))
        (jointEventMass WeightPair.ideal (rationalGaussianBatch a b halves) E *
          jointTotal WeightPair.impl (rationalGaussianBatch a b halves)) * 2 ^ 168 <
      jointTotal WeightPair.impl (rationalGaussianBatch a b halves) *
        jointTotal WeightPair.ideal (rationalGaussianBatch a b halves) :=
  q192_rlwe_batch_event_transfer _ (by rw [List.length_map]; exact hLen)
    (rationalGaussianBatch_coords a b hq halves hHalves) E

/-- The pair tail event `‖z‖_2^2 > 1_500_000_000` over 2048 coordinates of one kind: its
    probability under the production law is within `2^-173` of its probability under the
    discrete Gaussian with any rational base in the enclosure. -/
theorem q192_rlwe_pair_l2_tail_transfer_rational_base (a b : Nat) (hq : InExpNegEnclosure a b)
    (half : Nat) (hHalf : half = 3070 ∨ half = 3072) :
    Spec.natAbsDiff
        (jointEventMass WeightPair.impl (rationalGaussianBatch a b (List.replicate 2048 half))
            (fun v => decide (1500000000 < centeredSqNorm half v)) *
          jointTotal WeightPair.ideal (rationalGaussianBatch a b (List.replicate 2048 half)))
        (jointEventMass WeightPair.ideal (rationalGaussianBatch a b (List.replicate 2048 half))
            (fun v => decide (1500000000 < centeredSqNorm half v)) *
          jointTotal WeightPair.impl (rationalGaussianBatch a b (List.replicate 2048 half))) *
        2 ^ 173 <
      jointTotal WeightPair.impl (rationalGaussianBatch a b (List.replicate 2048 half)) *
        jointTotal WeightPair.ideal (rationalGaussianBatch a b (List.replicate 2048 half)) := by
  have hSq : half * half < 2 ^ 24 := by
    rcases hHalf with r | r <;> subst r <;> decide
  refine q192_rlwe_pair_l2_tail_transfer half hHalf _
    (by rw [List.length_map, List.length_replicate]) (fun c hc => ?_)
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hc
  have hEq : h = half := List.eq_of_mem_replicate hh
  subst hEq
  exact ⟨rfl, rationalGaussian_idealBracket h hSq a b hq⟩

#verify_constructive
  Qsag.gaussianExpProbability_zero
  Qsag.gaussianExpProbability_succ
  Qsag.bitSelProd_zero
  Qsag.bitSelProd_succ
  Qsag.bitCount_zero
  Qsag.bitCount_succ
  Qsag.bitCount_le
  Qsag.bitSelProd_const_pow
  Qsag.bitSelProd_pad_self
  Qsag.bitSelProd_pos
  Qsag.rlweGaussianExpPowers_length
  Qsag.gaussianExpPower_succ_le
  Qsag.gaussianExpProbability_reference_values
  Qsag.gaussianExpProbability_bracket
  Qsag.gaussianExpProbability_le
  Qsag.IsFinSum.zero
  Qsag.IsFinSum.mul_left
  Qsag.IsFinSum.mul_right
  Qsag.IsFinSum.const
  Qsag.IsFinSum.natAbsDiff_le
  Qsag.IsFinSum.split
  Qsag.IsFinSum.nest
  Qsag.sampleSum_isFinSum
  Qsag.coordSum_succ
  Qsag.coordSum_isFinSum
  Qsag.coordSum_one
  Qsag.coordSum_lt_indicator
  Qsag.coordSum_point_indicator
  Qsag.coordSum_truncate
  Qsag.coordSum_eq_weightPrefixSum
  Qsag.IsFinSum.cross_l1_le_of_bracket
  Qsag.IsFinSum.total_le_of_bracket
  Qsag.IsFinSum.cross_l1_prod_le
  Qsag.IsFinSum.event_cross_le
  Qsag.thresholdGame_winCount
  Qsag.q192_accepting_coin_count
  Qsag.q192BernoulliGame_winCount
  Qsag.q192BernoulliGame_winProb
  Qsag.q192BernoulliAccept_eq_fastFiltered
  Qsag.q192_sampler_pointwise_error_le_pow2_neg192
  Qsag.q192_sampler_pointwise_error_ratBound
  Qsag.q192_gaussian_accept_pointwise_error_61_ulp
  Qsag.coordL1_eq
  Qsag.coordL1_mk
  Qsag.jointL1_eq
  Qsag.coordEventMass_eq
  Qsag.jointEventMass_eq
  Qsag.jointSum_isFinSum
  Qsag.jointSum_jointWeight
  Qsag.jointTotal_pos
  Qsag.jointL1_cons_le
  Qsag.jointL1_mul_le
  Qsag.coordEvent_cross_le
  Qsag.jointEvent_cross_le
  Qsag.gaussianBoxPair_eq
  Qsag.gaussianIdealBracket_iff
  Qsag.gaussianBoxTotal_3070
  Qsag.gaussianBoxTotal_3072
  Qsag.gaussianBoxTotal_lower
  Qsag.gaussianBox_idealTotal_pos
  Qsag.gaussianBox_coordL1_le
  Qsag.q192_gaussian_coordinate_tvd_bound
  Qsag.q192_gaussian_coordinate_event_transfer
  Qsag.gaussianBatch_eq
  Qsag.gaussianBatch_jointL1_le
  Qsag.gaussianBatch_totals_pos
  Qsag.gaussianBatch_tvd_lt
  Qsag.q192_rlwe_batch_tvd_bound
  Qsag.q192_rlwe_poly_batch_tvd_bound
  Qsag.gaussianBatch_event_transfer
  Qsag.q192_rlwe_batch_event_transfer
  Qsag.centeredSqNorm_nil
  Qsag.centeredSqNorm_cons
  Qsag.q192_rlwe_pair_l2_tail_transfer
  Qsag.gaussianBoxTrial_range
  Qsag.gaussianBoxTrial_response_inf_bound
  Qsag.gaussianBoxTrial_output_count
  Qsag.gaussianBoxTrial_accept_count
  Qsag.tooth_q8_truncation_violates_2pow_neg128_floor
  Qsag.tooth_q8_truncation_coordinate_tvd_exceeds_2pow_neg9
  Qsag.expNegTaylorNumer_zero
  Qsag.expNegTaylorNumer_succ
  Qsag.expNegTaylorDenom_zero
  Qsag.expNegTaylorDenom_succ
  Qsag.inExpNegEnclosure_iff
  Qsag.expNegEnclosure_nonempty_and_narrow
  Qsag.rlweGaussianExpPowers_floor_of_rational_base
  Qsag.bitSelProd_pow_two_pow
  Qsag.gaussianExpProbability_rational_base
  Qsag.q192_sampler_pointwise_error_rational_base
  Qsag.rationalGaussianWeight_eq
  Qsag.rationalGaussian_idealBracket
  Qsag.rationalGaussianBatch_eq
  Qsag.q192_rlwe_batch_tvd_bound_rational_base
  Qsag.q192_rlwe_batch_event_transfer_rational_base
  Qsag.q192_rlwe_pair_l2_tail_transfer_rational_base

end Qsag
end

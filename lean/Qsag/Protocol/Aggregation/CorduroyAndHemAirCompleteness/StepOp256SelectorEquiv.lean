module
/-
# No-Wrap Limb Lemmas, Guard/Transition Decomposition and the Selector-Muxed 256-Column `StepOp` Table

Polymorphic no-wrap backward unpacking and `< 2^63` limb decomposition lemmas, exact guard / functional-transition decomposition for every scheduled opcode, the equivalence
of the selector-explicit table with the original 256-column table
(`hemStepTraceValid_iff_stepOp256TableOk`), and the per-signer row semantics of an active slot.
-/

public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.CorduroyThresholdEngine

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
set_option autoImplicit false
set_option maxErrors 1000
set_option Elab.async false
set_option exponentiation.threshold 2048
attribute [local irreducible] poseidon2Perm12

/-! ## §3. Full Deployed 256-Column `Hem` `StepOp` AIR Completeness, Constructive Extraction & WHIR Wiring -/

section HemStepOp256Machine

local infixl:65 " +ₚ " => Goldilocks.add
local infixl:65 " -ₚ " => Goldilocks.sub
local infixl:70 " *ₚ " => Goldilocks.mul
local notation "‹" n "›" => Goldilocks.ofNat n

theorem g_add_zero (a : Goldilocks) : a +ₚ Goldilocks.zero = a :=
  LawfulCommRing.add_zero a
theorem g_zero_add (a : Goldilocks) : Goldilocks.zero +ₚ a = a :=
  LawfulCommRing.zero_add a
theorem g_add_assoc (a b c : Goldilocks) : (a +ₚ b) +ₚ c = a +ₚ (b +ₚ c) :=
  LawfulCommRing.add_assoc a b c
private theorem g_add_comm (a b : Goldilocks) : a +ₚ b = b +ₚ a :=
  LawfulCommRing.add_comm a b
private theorem g_mul_zero (a : Goldilocks) : a *ₚ Goldilocks.zero = Goldilocks.zero :=
  LawfulCommRing.mul_zero a
theorem g_zero_mul (a : Goldilocks) : Goldilocks.zero *ₚ a = Goldilocks.zero :=
  LawfulCommRing.zero_mul a
theorem g_mul_one (a : Goldilocks) : a *ₚ Goldilocks.one = a :=
  LawfulCommRing.mul_one a
theorem g_one_mul (a : Goldilocks) : Goldilocks.one *ₚ a = a :=
  LawfulCommRing.one_mul a
private theorem g_mul_assoc (a b c : Goldilocks) : (a *ₚ b) *ₚ c = a *ₚ (b *ₚ c) :=
  LawfulCommRing.mul_assoc a b c
private theorem g_mul_comm (a b : Goldilocks) : a *ₚ b = b *ₚ a :=
  LawfulCommRing.mul_comm a b
theorem g_left_distrib (a b c : Goldilocks) : a *ₚ (b +ₚ c) = (a *ₚ b) +ₚ (a *ₚ c) :=
  LawfulCommRing.left_distrib a b c
theorem g_sub_self (a : Goldilocks) : a -ₚ a = Goldilocks.zero :=
  LawfulCommRing.sub_self a
theorem g_sub_eq_zero_iff {a b : Goldilocks} : a -ₚ b = Goldilocks.zero ↔ a = b :=
  LawfulCommRing.sub_eq_zero_iff
theorem g_ofNat_add (a b : Nat) : Goldilocks.ofNat (a + b) = ‹a› +ₚ ‹b› := by
  apply Goldilocks.ext
  rw [Goldilocks.ofNat_val, Goldilocks.add_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val,
      Nat.add_mod]
theorem g_ofNat_mul (a b : Nat) : Goldilocks.ofNat (a * b) = ‹a› *ₚ ‹b› := by
  apply Goldilocks.ext
  rw [Goldilocks.ofNat_val, Goldilocks.mul_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val,
      Nat.mul_mod]

/-! ### §3.1. Polymorphic No-Wrap Backward-Unpacking & `< 2^63` Limb Decomposition Lemmas -/

/-- Evaluate a little-endian digit list in base `B`: `d_0 + B * (d_1 + B * ...)`. -/
@[expose] def evalBaseDigits (B : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + B * evalBaseDigits B ds

theorem evalBaseDigits_lt_pow (B : Nat) (hB : 0 < B) :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < B) → evalBaseDigits B ds < B ^ ds.length
  | [], _ => by simp [evalBaseDigits]
  | d :: ds, hLt => by
    have hd : d < B := hLt d (List.mem_cons_self ..)
    have ih := evalBaseDigits_lt_pow B hB ds (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    dsimp only [evalBaseDigits, List.length_cons]
    rw [Nat.pow_succ, Nat.mul_comm _ B]
    have hLe : 1 + evalBaseDigits B ds ≤ B ^ ds.length := by omega
    calc d + B * evalBaseDigits B ds
      _ < B + B * evalBaseDigits B ds := Nat.add_lt_add_right hd _
      _ = B * (1 + evalBaseDigits B ds) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ B * B ^ ds.length := Nat.mul_le_mul_left B hLe

theorem evalBaseDigits_inj (B : Nat) (hB : 0 < B) :
    ∀ {ds1 ds2 : List Nat},
      ds1.length = ds2.length →
      (∀ d ∈ ds1, d < B) →
      (∀ d ∈ ds2, d < B) →
      evalBaseDigits B ds1 = evalBaseDigits B ds2 →
      ds1 = ds2
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hLen, _, _, _ => False.elim (Nat.succ_ne_zero _ hLen.symm)
  | _ :: _, [], hLen, _, _, _ => False.elim (Nat.succ_ne_zero _ hLen)
  | d1 :: r1, d2 :: r2, hLen, hLt1, hLt2, hEq => by
    have hd1 : d1 < B := hLt1 d1 (List.mem_cons_self ..)
    have hd2 : d2 < B := hLt2 d2 (List.mem_cons_self ..)
    dsimp only [evalBaseDigits] at hEq
    have hMod := congrArg (· % B) hEq
    rw [Nat.mul_comm B (evalBaseDigits B r1), Nat.mul_comm B (evalBaseDigits B r2),
        Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hd1, Nat.mod_eq_of_lt hd2] at hMod
    subst hMod
    have hCancel := Nat.add_left_cancel hEq
    have hSubEq : evalBaseDigits B r1 = evalBaseDigits B r2 :=
      Nat.eq_of_mul_eq_mul_left hB hCancel
    rw [evalBaseDigits_inj B hB (Nat.succ.inj hLen)
          (fun x hx => hLt1 x (List.mem_cons_of_mem _ hx))
          (fun x hx => hLt2 x (List.mem_cons_of_mem _ hx)) hSubEq]

/-- Multi-step in-field quotient-unpacking chain `p_m = ofNat d_m +ₚ (p_{m+1} *ₚ ofNat B)` ending at `qFinal`.
    Instantiates simultaneously to:
    - FORS index unpacking (`B = 256, k ≤ 6`, `256^6 = 2^48 < p`),
    - WOTS remaining-step unpacking (`B = 4, k ≤ 26`, `4^26 = 2^52 < p`),
    - FORS & XMSS Merkle cursor halving (`B = 2, k ∈ {4, 6, 8}`, `2^8 = 256 < p`). -/
@[expose] def UnpackChain (B : Nat) : Goldilocks → List Nat → Goldilocks → Prop
  | pEnd, [], qFinal => pEnd = qFinal
  | pCur, d :: rest, qFinal =>
    d < B ∧ ∃ pNext : Goldilocks,
      pCur = Goldilocks.ofNat d +ₚ (pNext *ₚ ‹B›) ∧
      UnpackChain B pNext rest qFinal

/-- **No-Wrap Backward-Unpacking Theorem (`baseBUnpackChain_backward`)**:
    Whenever an `UnpackChain B p0 ds Goldilocks.zero` ends at `0` with `B ^ ds.length < goldilocksPrime`,
    every intermediate field quotient is automatically canonical (`< B ^ (k - m) < p`, with ZERO
    need for separate per-row quotient range checks!) and `p0.val = evalBaseDigits B ds`. -/
theorem baseBUnpackChain_backward (B : Nat) (hB : 0 < B) :
    ∀ (ds : List Nat) (p0 : Goldilocks),
      B ^ ds.length < goldilocksPrime →
      UnpackChain B p0 ds Goldilocks.zero →
      p0.val = evalBaseDigits B ds ∧ p0.val < B ^ ds.length ∧ (∀ d ∈ ds, d < B)
  | [], p0, _, hChain => by
    dsimp only [UnpackChain] at hChain
    subst hChain
    exact ⟨rfl, by simp [Goldilocks.zero], fun _ h => False.elim (List.not_mem_nil h)⟩
  | d :: rest, p0, hPowLtP, hChain => by
    rcases hChain with ⟨hd, pNext, hp0, hSub⟩
    have hSubPowLe : B ^ rest.length ≤ B ^ (d :: rest).length :=
      Nat.pow_le_pow_right hB (Nat.le_succ _)
    have hBLtP : B < goldilocksPrime := by
      have hB1 : B ^ 1 ≤ B ^ (d :: rest).length :=
        Nat.pow_le_pow_right hB (by simp)
      rw [Nat.pow_one] at hB1
      exact Nat.lt_of_le_of_lt hB1 hPowLtP
    obtain ⟨hNextVal, hNextLt, hRestLt⟩ :=
      baseBUnpackChain_backward B hB rest pNext (Nat.lt_of_le_of_lt hSubPowLe hPowLtP) hSub
    have hdVal : (Goldilocks.ofNat d).val = d :=
      Nat.mod_eq_of_lt (Nat.lt_trans hd hBLtP)
    have hBVal : (Goldilocks.ofNat B).val = B :=
      Nat.mod_eq_of_lt hBLtP
    have hCombLt : d + pNext.val * B < B ^ (d :: rest).length := by
      dsimp only [List.length_cons]
      rw [Nat.pow_succ]
      have hLe : pNext.val + 1 ≤ B ^ rest.length := hNextLt
      calc d + pNext.val * B
        _ < B + pNext.val * B := Nat.add_lt_add_right hd _
        _ = (pNext.val + 1) * B := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        _ ≤ B ^ rest.length * B := Nat.mul_le_mul_right B hLe
    have hMulVal : (pNext *ₚ ‹B›).val = B * evalBaseDigits B rest := by
      rw [Goldilocks.mul_val, hBVal, Nat.mod_eq_of_lt
            (Nat.lt_of_le_of_lt (Nat.le_add_left _ d) (Nat.lt_trans hCombLt hPowLtP)),
          hNextVal, Nat.mul_comm]
    have hAddLtP : d + B * evalBaseDigits B rest < goldilocksPrime := by
      rw [Nat.mul_comm B, ← hNextVal]
      exact Nat.lt_trans hCombLt hPowLtP
    have hp0Val : p0.val = evalBaseDigits B (d :: rest) := by
      rw [hp0, Goldilocks.add_val, hdVal, hMulVal, Nat.mod_eq_of_lt hAddLtP]
      rfl
    refine ⟨hp0Val, ?_, ?_⟩
    · rw [hp0Val, evalBaseDigits, Nat.mul_comm B, ← hNextVal]
      exact hCombLt
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hTail
      · exact hd
      · exact hRestLt x hTail

theorem extractLimbBase4Digits_getElem :
    ∀ (count v i : Nat) (hi : i < (extractLimbBase4Digits count v).length),
      (extractLimbBase4Digits count v)[i]'hi = (v / 4 ^ i) % 4
  | 0, _, _, hi => False.elim (by simp [extractLimbBase4Digits_zero] at hi)
  | _ + 1, v, 0, _ => by simp [extractLimbBase4Digits_succ]
  | count + 1, v, i + 1, hi => by
    have hi' : i < (extractLimbBase4Digits count (v / 4)).length := by
      rw [extractLimbBase4Digits_length] at hi ⊢
      omega
    have hStep : (extractLimbBase4Digits (count + 1) v)[i + 1]'hi =
        (extractLimbBase4Digits count (v / 4))[i]'hi' := by simp only [extractLimbBase4Digits_succ, List.getElem_cons_succ]
    rw [hStep, extractLimbBase4Digits_getElem count (v / 4) i hi',
        Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 4]

private theorem evalGoldilocksBase4_snoc :
    ∀ (xs : List Goldilocks) (y : Goldilocks),
      evalGoldilocksBase4 (xs ++ [y]) =
        evalGoldilocksBase4 xs +ₚ (y *ₚ ‹4 ^ xs.length›)
  | [], y => by
    simp only [List.nil_append, evalGoldilocksBase4_nil, evalGoldilocksBase4_cons, List.length_nil, Nat.pow_zero]
    show y +ₚ (‹4› *ₚ Goldilocks.zero) = Goldilocks.zero +ₚ (y *ₚ ‹1›)
    have h1 : (‹1› : Goldilocks) = Goldilocks.one := Goldilocks.ext rfl
    rw [h1, g_mul_zero, g_add_zero, g_zero_add, g_mul_one]
  | x :: xs, y => by
    simp only [List.cons_append, evalGoldilocksBase4_cons, List.length_cons]
    show x +ₚ (‹4› *ₚ evalGoldilocksBase4 (xs ++ [y])) =
      (x +ₚ (‹4› *ₚ evalGoldilocksBase4 xs)) +ₚ (y *ₚ ‹4 ^ (xs.length + 1)›)
    rw [evalGoldilocksBase4_snoc xs y, g_left_distrib, g_add_assoc]
    congr 1
    have hPow : (‹4 ^ (xs.length + 1)› : Goldilocks) = ‹4› *ₚ ‹4 ^ xs.length› := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact g_ofNat_mul 4 (4 ^ xs.length)
    rw [hPow, ← g_mul_assoc, g_mul_comm ‹4› y, g_mul_assoc]

private theorem stepWeightedSum_pow4_eq_evalGoldilocksBase4 (f : Nat → Goldilocks) :
    ∀ (n : Nat),
      stepWeightedSum f (fun i => 4 ^ i) n = evalGoldilocksBase4 ((List.range n).map f)
  | 0 => by simp only [stepWeightedSum_eq, List.range_zero, List.foldl_nil, List.map_nil, evalGoldilocksBase4_nil]
  | n + 1 => by
    rw [stepWeightedSum_eq]
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.map_append, List.map_cons, List.map_nil, evalGoldilocksBase4_snoc,
        List.length_map, List.length_range]
    rw [← stepWeightedSum_eq]
    exact congrArg (· +ₚ (f n *ₚ ‹4 ^ n›)) (stepWeightedSum_pow4_eq_evalGoldilocksBase4 f n)

theorem stepBoolCheck_eq_zero_iff (b : Goldilocks) :
    stepBoolCheck b = Goldilocks.zero ↔ (b = Goldilocks.zero ∨ b = Goldilocks.one) := by
  simp only [stepBoolCheck_eq]
  constructor
  · intro h
    have h' : CommRingOps.mul b (Goldilocks.one -ₚ b) = CommRingOps.zero := h
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h' with h0 | h1
    · exact .inl h0
    · exact .inr (g_sub_eq_zero_iff.mp h1).symm
  · rintro (rfl | rfl)
    · exact g_zero_mul _
    · rw [g_sub_self, g_mul_zero]

/-- Canonical `< 2^63` base-4 characterization of `stepLimb63Decomp`. -/
theorem stepLimb63Decomp_allZero_iff (x : StepOpRowInputs) (l : Nat) :
    allZeroGoldilocks (stepLimb63Decomp x l) = true ↔
      (x.prev (stMainSponge + l)).val < 2 ^ 63 ∧
      (∀ i < 31, x.aux i = Goldilocks.ofNat (((x.prev (stMainSponge + l)).val / 4 ^ i) % 4)) ∧
      x.aux 31 = Goldilocks.ofNat ((x.prev (stMainSponge + l)).val / 4 ^ 31) := by
  let v := x.prev (stMainSponge + l)
  let w : Limb63DecompWitness :=
    { limbVal := v
      digits  := (List.range 31).map x.aux
      topBit  := x.aux 31 }
  have hPow62 : (‹2 ^ 62› : Goldilocks) = ‹4 ^ 31› := rfl
  have hTail2 : ∀ (r0 r1 : Goldilocks),
      allZeroGoldilocks [r0, r1] = ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero)) := by
    intros; simp [allZeroGoldilocks_eq]
  have hHead3 : ∀ (r0 r1 r2 : Goldilocks) (rest : List Goldilocks),
      allZeroGoldilocks ([r0, r1, r2] ++ rest) =
        ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero) &&
         (r2 == Goldilocks.zero) && allZeroGoldilocks rest) := by
    intros; simp [allZeroGoldilocks_eq, Bool.and_assoc]
  have hEquiv : allZeroGoldilocks (stepLimb63Decomp x l) = true ↔
      allZeroGoldilocks (limb63DecompResiduals v w) = true := by
    simp only [stepLimb63Decomp_eq, limb63DecompResiduals.public_eqs]
    dsimp only [w]
    have hLen : (((List.range 31).map x.aux).length == 31) = true := by simp
    rw [hLen, List.map_map]
    simp only [↓reduceIte, allZeroGoldilocks_append, hTail2, hHead3, Bool.and_eq_true,
      beq_iff_eq, g_sub_self, true_and, stepBoolCheck_eq_zero_iff,
      boolBitResidual_eq_zero_iff, g_sub_eq_zero_iff,
      stepWeightedSum_pow4_eq_evalGoldilocksBase4, hPow62]
    have hMapEq : ((List.range 31).map (quarticBase4 ∘ x.aux)) =
        (List.range 31).map (fun i => quarticBase4 (x.aux i)) := rfl
    rw [hMapEq]
    constructor
    · rintro ⟨hQuart, hBit, hEq⟩
      refine ⟨⟨hBit, ?_⟩, hQuart⟩
      rw [g_mul_comm (‹4 ^ 31›) (x.aux 31)]
      exact hEq.symm
    · rintro ⟨⟨hBit, hEq⟩, hQuart⟩
      refine ⟨hQuart, hBit, ?_⟩
      rw [g_mul_comm (x.aux 31) (‹4 ^ 31›)]
      exact hEq.symm
  rw [hEquiv, limb63DecompResiduals_allZero_iff]
  constructor
  · rintro ⟨hLt, hWEq⟩
    have hDigEq := congrArg Limb63DecompWitness.digits hWEq
    have hTopEq := congrArg Limb63DecompWitness.topBit hWEq
    simp only [w, honestLimb63DecompWitness.public_eqs] at hDigEq hTopEq
    refine ⟨hLt, fun i hi => ?_, hTopEq⟩
    have hGet := congrArg (fun ls => ls.getD i Goldilocks.zero) hDigEq
    have hiL1 : i < ((List.range 31).map x.aux).length := by simp [hi]
    have hiExt : i < (extractLimbBase4Digits 31 v.val).length := by
      rw [extractLimbBase4Digits_length]; exact hi
    have hiL2 : i < ((extractLimbBase4Digits 31 v.val).map Goldilocks.ofNat).length := by
      simp [hiExt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL1, Option.getD_some,
        List.getElem_map, List.getElem_range,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL2, Option.getD_some,
        List.getElem_map, extractLimbBase4Digits_getElem 31 v.val i hiExt] at hGet
    exact hGet
  · rintro ⟨hLt, hAux, hTop⟩
    refine ⟨hLt, ?_⟩
    simp only [w, honestLimb63DecompWitness.public_eqs]
    rw [hTop]
    congr 1
    apply List.ext_getElem
    · simp [extractLimbBase4Digits_length]
    · intro i hi1 hi2
      have hi31 : i < 31 := by simpa using hi1
      have hiExt : i < (extractLimbBase4Digits 31 v.val).length := by
        rw [extractLimbBase4Digits_length]; exact hi31
      rw [List.getElem_map, List.getElem_range, List.getElem_map,
          extractLimbBase4Digits_getElem 31 v.val i hiExt]
      exact hAux i hi31

theorem stepByteVal_eq_of_limb63 (x : StepOpRowInputs) (l sub : Nat)
    (hSub : sub < 7)
    (hDecomp : allZeroGoldilocks (stepLimb63Decomp x l) = true) :
    stepByteVal x sub =
      Goldilocks.ofNat (((x.prev (stMainSponge + l)).val / 256 ^ sub) % 256) := by
  obtain ⟨_, hAux, _⟩ := (stepLimb63Decomp_allZero_iff x l).mp hDecomp
  let v := (x.prev (stMainSponge + l)).val
  have e0 := hAux (4 * sub) (by omega)
  have e1 := hAux (4 * sub + 1) (by omega)
  have e2 := hAux (4 * sub + 2) (by omega)
  have e3 := hAux (4 * sub + 3) (by omega)
  simp only [stepByteVal_eq]
  rw [e0, e1, e2, e3]
  simp only [← g_ofNat_mul, ← g_ofNat_add]
  apply congrArg Goldilocks.ofNat
  have hPow0 : 4 ^ (4 * sub) = 256 ^ sub := by
    rw [Nat.pow_mul]
  have hPow1 : 4 ^ (4 * sub + 1) = 256 ^ sub * 4 := by
    rw [Nat.pow_add, hPow0]
  have hPow2 : 4 ^ (4 * sub + 2) = 256 ^ sub * 16 := by
    rw [Nat.pow_add, hPow0]
  have hPow3 : 4 ^ (4 * sub + 3) = 256 ^ sub * 64 := by
    rw [Nat.pow_add, hPow0]
  rw [hPow0, hPow1, hPow2, hPow3,
      ← Nat.div_div_eq_div_mul v (256 ^ sub) 4,
      ← Nat.div_div_eq_div_mul v (256 ^ sub) 16,
      ← Nat.div_div_eq_div_mul v (256 ^ sub) 64]
  generalize v / 256 ^ sub = w
  omega

theorem stepLow4Bits_eq_of_limb63 (x : StepOpRowInputs) (l : Nat)
    (hDecomp : allZeroGoldilocks (stepLimb63Decomp x l) = true) :
    x.aux 0 +ₚ (x.aux 1 *ₚ ‹4›) =
      Goldilocks.ofNat ((x.prev (stMainSponge + l)).val % 16) := by
  obtain ⟨_, hAux, _⟩ := (stepLimb63Decomp_allZero_iff x l).mp hDecomp
  rw [hAux 0 (by decide), hAux 1 (by decide)]
  simp only [← g_ofNat_mul, ← g_ofNat_add, Nat.pow_zero, Nat.pow_one, Nat.div_one]
  apply congrArg Goldilocks.ofNat
  omega

private theorem evalBase4Digits_map_div_mod :
    ∀ (n w : Nat),
      evalBase4Digits ((List.range n).map (fun i => (w / 4 ^ i) % 4)) = w % (4 ^ n)
  | 0, w => by simp [evalBase4Digits_nil, Nat.mod_one]
  | n + 1, w => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [evalBase4Digits_cons]
    have hShift :
        (List.range n).map ((fun i => (w / 4 ^ i) % 4) ∘ Nat.succ) =
        (List.range n).map (fun i => ((w / 4) / 4 ^ i) % 4) := by
      congr 1; funext i
      dsimp only [Function.comp]
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 4]
    rw [hShift, evalBase4Digits_map_div_mod n (w / 4), Nat.pow_zero, Nat.div_one, Nat.pow_succ]
    have hPowPos : 0 < 4 ^ n := Nat.pow_pos (by decide)
    have hRemLt : (w / 4) % 4 ^ n < 4 ^ n := Nat.mod_lt _ hPowPos
    have hW : w = (w % 4 + 4 * ((w / 4) % 4 ^ n)) + ((w / 4) / 4 ^ n) * (4 ^ n * 4) := by
      have h1 := (Nat.mod_add_div w 4).symm
      have h2 := (Nat.mod_add_div (w / 4) (4 ^ n)).symm
      calc w
        _ = w % 4 + 4 * (w / 4) := h1
        _ = w % 4 + 4 * ((w / 4) % 4 ^ n + 4 ^ n * ((w / 4) / 4 ^ n)) := by rw [← h2]
        _ = (w % 4 + 4 * ((w / 4) % 4 ^ n)) + ((w / 4) / 4 ^ n) * (4 ^ n * 4) := by
          rw [Nat.mul_add, Nat.add_assoc]
          congr 1
          rw [← Nat.mul_assoc, Nat.mul_comm (4 * 4 ^ n), Nat.mul_comm 4 (4 ^ n)]
    conv => rhs; rw [hW, Nat.add_mul_mod_self_right]
    exact (Nat.mod_eq_of_lt (by omega)).symm

theorem stepHi28_eq_of_limb63 (x : StepOpRowInputs) (l : Nat)
    (hDecomp : allZeroGoldilocks (stepLimb63Decomp x l) = true) :
    stepHi28 x = Goldilocks.ofNat (((x.prev (stMainSponge + l)).val % 2 ^ 32) / 16) := by
  obtain ⟨_, hAux, _⟩ := (stepLimb63Decomp_allZero_iff x l).mp hDecomp
  let v := (x.prev (stMainSponge + l)).val
  simp only [stepHi28_def]
  rw [stepWeightedSum_pow4_eq_evalGoldilocksBase4]
  let ds := (List.range 14).map (fun i => x.aux (2 + i))
  have hDsEq : ds = (List.range 14).map (fun i => Goldilocks.ofNat (((v / 16) / 4 ^ i) % 4)) := by
    apply List.ext_getElem
    · simp [ds]
    · intro i hi1 _
      have hi14 : i < 14 := by simpa [ds] using hi1
      simp only [ds, List.getElem_map, List.getElem_range]
      rw [hAux (2 + i) (by omega)]
      apply congrArg Goldilocks.ofNat
      have hPow : 4 ^ (2 + i) = 16 * 4 ^ i := by
        rw [Nat.pow_add]
      rw [hPow, ← Nat.div_div_eq_div_mul]
  have h4LtP : 4 < goldilocksPrime := by decide
  have hDsLt4 : ∀ d ∈ ds, d.val < 4 := by
    rw [hDsEq]
    intro d hd
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
    rw [Goldilocks.ofNat_val, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) h4LtP)]
    exact Nat.mod_lt _ (by decide)
  apply Goldilocks.ext
  rw [evalGoldilocksBase4_val_of_lt4 ds (by simp [ds]) hDsLt4, hDsEq, List.map_map]
  have hMapVal :
      (List.range 14).map (Goldilocks.val ∘ fun i => Goldilocks.ofNat (((v / 16) / 4 ^ i) % 4)) =
      (List.range 14).map (fun i => ((v / 16) / 4 ^ i) % 4) := by
    congr 1; funext i
    dsimp only [Function.comp]
    rw [Goldilocks.ofNat_val]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) h4LtP)
  rw [hMapVal, evalBase4Digits_map_div_mod 14 (v / 16)]
  have hPow14 : (4 : Nat) ^ 14 = 2 ^ 28 := rfl
  have hPow32 : (2 : Nat) ^ 32 = 16 * 2 ^ 28 := rfl
  rw [hPow14]
  have hLtP : (v % 2 ^ 32) / 16 < goldilocksPrime := by
    have : v % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have : (2 : Nat) ^ 28 < goldilocksPrime := by decide
    omega
  rw [Goldilocks.ofNat_val, Nat.mod_eq_of_lt hLtP]
  have hDivMod : (v / 16) % (2 ^ 28) = (v % (16 * 2 ^ 28)) / 16 := by
    have h1 := (Nat.mod_add_div v (16 * 2 ^ 28)).symm
    conv => lhs; rw [h1]
    have hRew : v % (16 * 2 ^ 28) + 16 * 2 ^ 28 * (v / (16 * 2 ^ 28)) =
        v % (16 * 2 ^ 28) + ((2 ^ 28) * (v / (16 * 2 ^ 28))) * 16 := by
      congr 1
      simp only [Nat.mul_assoc, Nat.mul_comm]
    rw [hRew, Nat.add_mul_div_right _ _ (by decide), Nat.add_mul_mod_self_left]
    have hRemLt : (v % (16 * 2 ^ 28)) / 16 < 2 ^ 28 := by
      have : v % (16 * 2 ^ 28) < 16 * 2 ^ 28 := Nat.mod_lt _ (by decide)
      omega
    exact Nat.mod_eq_of_lt hRemLt
  rw [← hPow32] at hDivMod
  exact hDivMod

/-! ### §3.2. Guard/Transition Decomposition & Selector-Muxed 256-Column `StepOp` Equivalence -/

/-- Pure guard residuals of `stepMerkleBlockA` (independent of `x.next`). -/
@[expose] def stepMerkleBlockAGuards (x : StepOpRowInputs) (domainTag meta0 : Goldilocks) : List Goldilocks :=
  [stepBoolCheck (x.aux 0), x.prev stCursorIdx -ₚ ((x.aux 0 +ₚ x.aux 1) +ₚ x.aux 1)] ++
  (List.range 4).flatMap (fun i =>
    [x.stIn i -ₚ x.pkSeed i,
     x.stIn (4 + i) -ₚ
       (((Goldilocks.one -ₚ x.aux 0) *ₚ x.prev (stWork + i)) +ₚ (x.aux 0 *ₚ x.aux (2 + i)))]) ++
  [x.stIn 8 -ₚ domainTag, x.stIn 9 -ₚ meta0, x.stIn 10 -ₚ x.prev stTreeLo,
   x.stIn 11 -ₚ x.prev stTreeHi]

/-- Functional next-state of `stepMerkleBlockA` (independent of `x.next`). -/
@[expose] def stepMerkleBlockAExpectedNext (x : StepOpRowInputs) (j : Nat) : Goldilocks :=
  if stepInBlock stSubSponge 12 j then x.permOut (j - stSubSponge)
  else if stepInBlock stWork 4 j then
    let i := j - stWork
    (x.aux 0 *ₚ x.prev (stWork + i)) +ₚ ((Goldilocks.one -ₚ x.aux 0) *ₚ x.aux (2 + i))
  else if j = stCursorIdx then x.aux 1
  else x.prev j

/-- Pure pre-state / `stIn` / `permOut` / `aux` guard residuals of one `StepConstraintKind`
    (never reads `x.next`). -/
@[expose] def stepOpGuardResiduals (kind : StepConstraintKind) (c0 : Goldilocks) (x : StepOpRowInputs) :
    List Goldilocks :=
  match kind with
  | .idle => []
  | .statefulHmsgBlock0 =>
    (List.range 6).map (fun i => stepBoolCheck (x.aux i)) ++
    (List.range 32).map (fun i => stepBoolCheck (x.aux (6 + i))) ++
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgStateful,
     x.stIn 9 -ₚ ((stepWeightedSum x.aux (fun i => 2 ^ i) 6 *ₚ ‹2 ^ 32›) +ₚ
       stepWeightedSum (fun i => x.aux (6 + i)) (fun i => 2 ^ i) 32),
     x.stIn 10 -ₚ x.mu 4, x.stIn 11 -ₚ poseidon2IvTag]
  | .statefulHmsgBlock1 => stepSpongeAbsorbInput x x.aux x.mu
  | .statefulHmsgSqueeze => stepSqueezeInput x
  | .statelessDeriveBlock0 =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgStateless, x.stIn 9 -ₚ x.mu 4, x.stIn 10,
     x.stIn 11 -ₚ poseidon2IvTag]
  | .statelessDeriveBlock1 => stepSpongeAbsorbInput x x.aux x.mu
  | .statelessDecompLimb l => stepLimb63Decomp x l
  | .forsRootsSpongeInit =>
    (List.range 4).map (fun i => x.stIn i -ₚ x.pkSeed i) ++
    [x.stIn 4 -ₚ x.prev stKpIdx, x.stIn 5 -ₚ x.prev stTreeLo, x.stIn 6 -ₚ x.prev stTreeHi,
     x.stIn 7 -ₚ ‹32›, x.stIn 8 -ₚ domainForsRoots, x.stIn 9, x.stIn 10,
     x.stIn 11 -ₚ poseidon2IvTag]
  | .forsLeafHash slot =>
    (List.range 4).map (fun k => quarticBase4 (x.aux (4 + k))) ++
    [x.prev (stRemPack + slot) -ₚ
       (stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4 +ₚ (x.aux 8 *ₚ ‹256›))] ++
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.aux i, x.stIn (4 + i) -ₚ x.pkSeed i]) ++
    [x.stIn 8 -ₚ domainForsLeaf,
     x.stIn 9 -ₚ ((x.prev stKpIdx *ₚ ‹2 ^ 24›) +ₚ
       (c0 +ₚ stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4)),
     x.stIn 10 -ₚ x.prev stTreeLo, x.stIn 11 -ₚ x.prev stTreeHi]
  | .forsMerkleBlockA =>
    stepMerkleBlockAGuards x domainForsNode ((c0 +ₚ (x.prev stKpIdx *ₚ ‹2 ^ 16›)) +ₚ x.aux 1)
  | .forsMerkleBlockB isTreeLast _ =>
    stepMerkleBlockBInput x ++ (if isTreeLast then [x.prev stCursorIdx] else [])
  | .forsRootsPairAbsorb isLastPair =>
    (if isLastPair then (List.range 6).map (fun s => x.prev (stRemPack + s)) else []) ++
    stepSpongeAbsorbInput x (fun i => x.prev (stCurRoot + i)) (fun i => x.prev (stWork + i))
  | .forsRootsFinalSqueeze => stepSqueezeInput x
  | .detTreeHmsgBlock0 =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgDetTree, x.stIn 9 -ₚ (c0 +ₚ x.prev stKpIdx),
     x.stIn 10 -ₚ x.prev stTreeLo, x.stIn 11 -ₚ x.prev stTreeHi]
  | .detTreeHmsgBlock1 =>
    (List.range 32).map (fun i => stepBoolCheck (x.aux i)) ++
    (List.range 4).map (fun i =>
      x.stIn i -ₚ (x.prev (stMainSponge + i) +ₚ x.prev (stCurRoot + i))) ++
    [x.stIn 4 -ₚ (x.prev (stMainSponge + 4) +ₚ stepWeightedSum x.aux (fun i => 2 ^ i) 32),
     x.stIn 5 -ₚ (x.prev (stMainSponge + 5) +ₚ Goldilocks.one)] ++
    (List.range 6).map (fun i => x.stIn (6 + i) -ₚ x.prev (stMainSponge + 6 + i))
  | .hmsgDecompLimb l =>
    stepLimb63Decomp x l ++
    (if l = 4 then [stepHmsgDecompExpected x l stAccOrU1 -ₚ ‹192›] else [])
  | .wotsTellInit =>
    (List.range 4).map (fun i => x.stIn i -ₚ x.pkSeed i) ++
    [x.stIn 4 -ₚ (c0 +ₚ x.prev stKpIdx), x.stIn 5 -ₚ x.prev stTreeLo,
     x.stIn 6 -ₚ x.prev stTreeHi, x.stIn 7 -ₚ ‹128›, x.stIn 8 -ₚ domainWotsPk, x.stIn 9,
     x.stIn 10, x.stIn 11 -ₚ poseidon2IvTag]
  | .wotsChainStep0 slot =>
    [stepBoolCheck (x.aux 4), stepBoolCheck (x.aux 5), stepBoolCheck (x.aux 6),
     x.aux 5 *ₚ (Goldilocks.one -ₚ x.aux 4), x.aux 6 *ₚ (Goldilocks.one -ₚ x.aux 5),
     x.prev (stRemPack + slot) -ₚ
       ((‹3› -ₚ ((x.aux 4 +ₚ x.aux 5) +ₚ x.aux 6)) +ₚ (x.aux 7 *ₚ ‹4›))] ++
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.aux i, x.stIn (4 + i) -ₚ x.pkSeed i]) ++
    stepWotsStepInput x c0
  | .wotsChainStep1 =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.prev (stWork + i), x.stIn (4 + i) -ₚ x.pkSeed i]) ++
    stepWotsStepInput x c0
  | .wotsChainStep2 _ =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.prev (stWork + i), x.stIn (4 + i) -ₚ x.pkSeed i]) ++
    stepWotsStepInput x c0
  | .wotsTellPairAbsorb isLastPair =>
    (if isLastPair then (List.range 5).map (fun s => x.prev (stRemPack + s)) else []) ++
    stepSpongeAbsorbInput x (fun i => x.prev (stSubSponge + i)) (fun i => x.prev (stWork + i))
  | .wotsTellFinalSqueeze => stepSqueezeInput x
  | .xmssMerkleBlockA =>
    stepMerkleBlockAGuards x domainMerkleNode (c0 +ₚ x.aux 1)
  | .xmssMerkleBlockB isLayerLast isTopFinal =>
    stepMerkleBlockBInput x ++
    (if !isLayerLast then []
     else if isTopFinal then
       [x.prev stCursorIdx] ++ (List.range 4).map (fun i => x.permOut i -ₚ x.pkRoot i)
     else
       [x.prev stCursorIdx] ++
       (List.range 4).map (fun i => stepBoolCheck (x.aux i)) ++
       (List.range 14).map (fun i => quarticBase4 (x.aux (4 + i))) ++
       (List.range 2).map (fun i => quarticBase4 (x.aux (18 + i))) ++
       (List.range 14).map (fun i => quarticBase4 (x.aux (20 + i))) ++
       [x.prev stTreeLo -ₚ
          (stepWeightedSum x.aux (fun i => 2 ^ i) 4 +ₚ
            (stepWeightedSum (fun i => x.aux (4 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›)),
        x.prev stTreeHi -ₚ
          (stepWeightedSum (fun i => x.aux (18 + i)) (fun i => 4 ^ i) 2 +ₚ
            (stepWeightedSum (fun i => x.aux (20 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›))])

/-- Deterministic next-state limb `j` (`0 ≤ j < 44`) of one `StepConstraintKind` (never reads `x.next`). -/
@[expose] def stepOpExpectedNext (kind : StepConstraintKind) (_c0 : Goldilocks) (x : StepOpRowInputs)
    (j : Nat) : Goldilocks :=
  match kind with
  | .idle => Goldilocks.zero
  | .statefulHmsgBlock0 =>
    if stepInBlock stCurRoot 4 j then x.pkRoot (j - stCurRoot)
    else if j = stKpIdx then stepWeightedSum x.aux (fun i => 2 ^ i) 6
    else if stepInBlock stMainSponge 12 j then x.permOut (j - stMainSponge)
    else Goldilocks.zero
  | .statefulHmsgBlock1 | .forsRootsSpongeInit | .forsRootsPairAbsorb _
  | .detTreeHmsgBlock0 | .wotsTellInit | .wotsTellPairAbsorb _ =>
    if stepInBlock stMainSponge 12 j then x.permOut (j - stMainSponge) else x.prev j
  | .statefulHmsgSqueeze | .detTreeHmsgBlock1 =>
    if stepInBlock stRemPack 6 j then Goldilocks.zero
    else if stepInBlock stMainSponge 12 j then x.permOut (j - stMainSponge)
    else if j = stAccOrU1 then Goldilocks.zero
    else x.prev j
  | .statelessDeriveBlock0 =>
    if stepInBlock stMainSponge 12 j then x.permOut (j - stMainSponge) else Goldilocks.zero
  | .statelessDeriveBlock1 =>
    if stepInBlock stMainSponge 12 j then x.permOut (j - stMainSponge)
    else if stepInBlock stRemPack 6 j then Goldilocks.zero
    else x.prev j
  | .statelessDecompLimb l => stepStatelessDecompExpected x l j
  | .forsLeafHash slot =>
    if j = stRemPack + slot then x.aux 8
    else if stepInBlock stWork 4 j then
      let i := j - stWork
      x.permOut i +ₚ ((x.aux i +ₚ (‹2› *ₚ x.stIn (4 + i))) +ₚ (‹4› *ₚ x.stIn (8 + i)))
    else if j = stCursorIdx then stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4
    else x.prev j
  | .forsMerkleBlockA | .xmssMerkleBlockA => stepMerkleBlockAExpectedNext x j
  | .forsMerkleBlockB isTreeLast isOddTree =>
    if isTreeLast && !isOddTree then
      if stepInBlock stCurRoot 4 j then x.permOut (j - stCurRoot) else x.prev j
    else
      if stepInBlock stWork 4 j then x.permOut (j - stWork) else x.prev j
  | .forsRootsFinalSqueeze =>
    if stepInBlock stCurRoot 4 j then x.permOut (j - stCurRoot) else x.prev j
  | .hmsgDecompLimb l => stepHmsgDecompExpected x l j
  | .wotsChainStep0 slot =>
    if j = stRemPack + slot then x.aux 7
    else if stepInBlock stWork 4 j then
      let i := j - stWork
      (x.aux 4 *ₚ x.aux i) +ₚ ((Goldilocks.one -ₚ x.aux 4) *ₚ
        (x.permOut i +ₚ ((x.aux i +ₚ (‹2› *ₚ x.stIn (4 + i))) +ₚ (‹4› *ₚ x.stIn (8 + i)))))
    else if j = stAccOrU1 then x.aux 5
    else if j = stWotsU2 then x.aux 6
    else x.prev j
  | .wotsChainStep1 =>
    if stepInBlock stWork 4 j then
      let i := j - stWork
      (x.prev stAccOrU1 *ₚ x.prev (stWork + i)) +ₚ
        ((Goldilocks.one -ₚ x.prev stAccOrU1) *ₚ
          (x.permOut i +ₚ ((x.prev (stWork + i) +ₚ (‹2› *ₚ x.stIn (4 + i))) +ₚ
            (‹4› *ₚ x.stIn (8 + i)))))
    else x.prev j
  | .wotsChainStep2 isOdd =>
    let base := if isOdd then stWork else stSubSponge
    if stepInBlock base 4 j then
      let i := j - base
      (x.prev stWotsU2 *ₚ x.prev (stWork + i)) +ₚ
        ((Goldilocks.one -ₚ x.prev stWotsU2) *ₚ
          (x.permOut i +ₚ ((x.prev (stWork + i) +ₚ (‹2› *ₚ x.stIn (4 + i))) +ₚ
            (‹4› *ₚ x.stIn (8 + i)))))
    else x.prev j
  | .wotsTellFinalSqueeze =>
    if stepInBlock stWork 4 j then x.permOut (j - stWork)
    else if j = stCursorIdx then x.prev stKpIdx
    else x.prev j
  | .xmssMerkleBlockB isLayerLast isTopFinal =>
    if !isLayerLast then
      if stepInBlock stWork 4 j then x.permOut (j - stWork) else x.prev j
    else if isTopFinal then
      Goldilocks.zero
    else
      if stepInBlock stCurRoot 4 j then x.permOut (j - stCurRoot)
      else if j = stKpIdx then stepWeightedSum x.aux (fun i => 2 ^ i) 4
      else if j = stTreeLo then
        stepWeightedSum (fun i => x.aux (4 + i)) (fun i => 4 ^ i) 14 +ₚ
          (stepWeightedSum (fun i => x.aux (18 + i)) (fun i => 4 ^ i) 2 *ₚ ‹2 ^ 28›)
      else if j = stTreeHi then
        stepWeightedSum (fun i => x.aux (20 + i)) (fun i => 4 ^ i) 14
      else x.prev j

theorem stepOpGuardResiduals_congr_next (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (next' : Nat → Goldilocks) :
    stepOpGuardResiduals kind c0 { x with next := next' } = stepOpGuardResiduals kind c0 x := by
  cases kind <;> simp only [stepOpGuardResiduals, stepSpongeAbsorbInput.public_eqs, stepSqueezeInput.public_eqs, stepMerkleBlockBInput.public_eqs, stepWotsStepInput.public_eqs, stepHmsgDecompExpected.public_eqs, stepLimb63Decomp_eq] <;> rfl

theorem stepOpExpectedNext_congr_next (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (next' : Nat → Goldilocks) (j : Nat) :
    stepOpExpectedNext kind c0 { x with next := next' } j = stepOpExpectedNext kind c0 x j := by
  cases kind <;> simp only [stepOpExpectedNext, stepStatelessDecompExpected_congr_next, stepHmsgDecompExpected_congr_next] <;> rfl

theorem allZero_map_iff (n : Nat) (f : Nat → Goldilocks) :
    allZeroGoldilocks ((List.range n).map f) = true ↔ ∀ i < n, f i = Goldilocks.zero := by
  simp only [allZeroGoldilocks_eq]
  rw [List.all_map, List.all_eq_true]
  constructor
  · intro h i hi; exact beq_iff_eq.mp (h i (List.mem_range.mpr hi))
  · intro h i hi; exact beq_iff_eq.mpr (h i (List.mem_range.mp hi))

private theorem allZero_stepNextIsPerm_iff (x : StepOpRowInputs) (base n : Nat) :
    allZeroGoldilocks (stepNextIsPerm x base n) = true ↔
      ∀ i < n, x.next (base + i) = x.permOut i := by
  simp only [stepNextIsPerm.public_eqs]
  rw [allZero_map_iff]
  simp only [g_sub_eq_zero_iff]

private theorem allZero_filterMap_range_iff (n : Nat) (skip : Nat → Bool) (f : Nat → Goldilocks) :
    allZeroGoldilocks ((List.range n).filterMap (fun j => if skip j then none else some (f j))) = true ↔
      ∀ j < n, skip j = false → f j = Goldilocks.zero := by
  simp only [allZeroGoldilocks_eq]
  rw [List.all_filterMap, List.all_eq_true]
  constructor
  · intro h j hj hSkip
    have hMem := h j (List.mem_range.mpr hj)
    simp only [hSkip, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hMem
    exact hMem
  · intro h j hj
    cases hSkip : skip j
    · simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
      exact h j (List.mem_range.mp hj) hSkip
    · rfl

private theorem allZero_stepCarryUnchanged_iff (x : StepOpRowInputs) (changed : Nat → Bool) :
    allZeroGoldilocks (stepCarryUnchanged x changed) = true ↔
      ∀ j < 44, changed j = false → x.next j = x.prev j := by
  simp only [stepCarryUnchanged.public_eqs]
  rw [allZero_filterMap_range_iff]
  simp only [g_sub_eq_zero_iff]

private theorem allZero_stepZeroElsewhere_iff (x : StepOpRowInputs) (kept : Nat → Bool) :
    allZeroGoldilocks (stepZeroElsewhere x kept) = true ↔
      ∀ j < 44, kept j = false → x.next j = Goldilocks.zero := by
  simp only [stepZeroElsewhere.public_eqs]
  exact allZero_filterMap_range_iff 44 kept x.next

private theorem allZero_flatMap_triple_iff (n : Nat) (g1 g2 nRes : Nat → Goldilocks) :
    allZeroGoldilocks ((List.range n).flatMap (fun i => [g1 i, g2 i, nRes i])) = true ↔
      allZeroGoldilocks ((List.range n).flatMap (fun i => [g1 i, g2 i])) = true ∧
      ∀ i < n, nRes i = Goldilocks.zero := by
  simp only [allZeroGoldilocks_eq]
  simp only [List.all_flatMap, List.all_cons, List.all_nil, Bool.and_true,
    List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact ⟨fun i hi => ⟨(h i hi).1, (h i hi).2.1⟩, fun i hi => (h i hi).2.2⟩
  · rintro ⟨hg, hn⟩ i hi
    exact ⟨(hg i hi).1, (hg i hi).2, hn i hi⟩

private theorem stepInBlock_iff (a n j : Nat) :
    stepInBlock a n j = true ↔ a ≤ j ∧ j < a + n := by
  simp only [stepInBlock.public_eqs]
  simp only [Bool.and_eq_true, decide_eq_true_eq]

private theorem stepMerkleBlockA_iff (x : StepOpRowInputs) (domainTag meta0 : Goldilocks) :
    allZeroGoldilocks (stepMerkleBlockA x domainTag meta0) = true ↔
      allZeroGoldilocks (stepMerkleBlockAGuards x domainTag meta0) = true ∧
      ∀ j < 44, x.next j = stepMerkleBlockAExpectedNext x j := by
  simp only [stepMerkleBlockA.public_eqs, stepMerkleBlockAGuards]
  have hSingle : ∀ r : Goldilocks, allZeroGoldilocks [r] = (r == Goldilocks.zero) := by
    intro r; simp [allZeroGoldilocks_eq]
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_flatMap_triple_iff,
    allZero_stepNextIsPerm_iff, hSingle, beq_iff_eq, g_sub_eq_zero_iff,
    allZero_stepCarryUnchanged_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨hG0, hG1, hNextWork⟩, hG2⟩, hNextSub⟩, hNextCur⟩, hCarry⟩
    refine ⟨⟨⟨hG0, hG1⟩, hG2⟩, fun j hj => ?_⟩
    unfold stepMerkleBlockAExpectedNext
    by_cases hSub : stepInBlock stSubSponge 12 j = true
    · rw [hSub]; simp only [↓reduceIte]
      obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stSubSponge 12 j).mp hSub
      have hi : j - stSubSponge < 12 := by simp only [stSubSponge.public_eqs] at *; omega
      have hAdd : stSubSponge + (j - stSubSponge) = j := by omega
      simpa only [hAdd] using hNextSub (j - stSubSponge) hi
    · have hSubF : stepInBlock stSubSponge 12 j = false := Bool.eq_false_iff.mpr hSub
      rw [hSubF]; simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hWk : stepInBlock stWork 4 j = true
      · rw [hWk]; simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hWk
        have hi : j - stWork < 4 := by simp only [stWork.public_eqs] at *; omega
        have hAdd : stWork + (j - stWork) = j := by omega
        simpa only [hAdd] using hNextWork (j - stWork) hi
      · have hWkF : stepInBlock stWork 4 j = false := Bool.eq_false_iff.mpr hWk
        rw [hWkF]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hCur : j = stCursorIdx
        · subst hCur; simp [hNextCur]
        · simp only [hCur, ↓reduceIte]
          exact hCarry j hj (by simp [hSubF, hWkF, beq_false_of_ne hCur])
  · rintro ⟨⟨⟨hG0, hG1⟩, hG2⟩, hNext⟩
    refine ⟨⟨⟨⟨⟨hG0, hG1, fun i hi => ?_⟩, hG2⟩, fun i hi => ?_⟩, ?_⟩, fun j hj hCh => ?_⟩
    · rw [hNext (stWork + i) (by simp only [stWork.public_eqs]; omega)]
      unfold stepMerkleBlockAExpectedNext
      have hSubF : stepInBlock stSubSponge 12 (stWork + i) = false := by
        simp only [stepInBlock.public_eqs, stSubSponge.public_eqs, stWork.public_eqs]; simp
      have hWkT : stepInBlock stWork 4 (stWork + i) = true := by
        simp only [stepInBlock.public_eqs, stWork.public_eqs]; simp; omega
      have hSubIdx : stWork + i - stWork = i := by omega
      simp [hSubF, hWkT, hSubIdx]
    · rw [hNext (stSubSponge + i) (by simp only [stSubSponge.public_eqs]; omega)]
      unfold stepMerkleBlockAExpectedNext
      have hSubT : stepInBlock stSubSponge 12 (stSubSponge + i) = true := by
        simp only [stepInBlock.public_eqs, stSubSponge.public_eqs]; simp; omega
      have hSubIdx : stSubSponge + i - stSubSponge = i := by omega
      simp [hSubT, hSubIdx]
    · rw [hNext stCursorIdx (by decide)]
      unfold stepMerkleBlockAExpectedNext
      have hSubF : stepInBlock stSubSponge 12 stCursorIdx = false := by decide
      have hWkF : stepInBlock stWork 4 stCursorIdx = false := by decide
      simp [hSubF, hWkF]
    · rw [hNext j hj]
      unfold stepMerkleBlockAExpectedNext
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
      simp [hCh.1.1, hCh.1.2, hCh.2]

private theorem stepBlockUpdate_iff (x : StepOpRowInputs) (base n : Nat)
    (hEnd : base + n ≤ 44) :
    (allZeroGoldilocks (stepNextIsPerm x base n) = true ∧
     allZeroGoldilocks (stepCarryUnchanged x (fun j => stepInBlock base n j)) = true) ↔
      ∀ j < 44, x.next j = (if stepInBlock base n j then x.permOut (j - base) else x.prev j) := by
  rw [allZero_stepNextIsPerm_iff, allZero_stepCarryUnchanged_iff]
  constructor
  · rintro ⟨hPerm, hCarry⟩ j hj
    cases hIn : stepInBlock base n j
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hCarry j hj hIn
    · simp only [↓reduceIte]
      obtain ⟨hLo, hHi⟩ := (stepInBlock_iff base n j).mp hIn
      have hAdd : base + (j - base) = j := by omega
      simpa only [hAdd] using hPerm (j - base) (by omega)
  · intro hNext
    refine ⟨fun i hi => ?_, fun j hj hCh => ?_⟩
    · rw [hNext (base + i) (by omega)]
      have hIn : stepInBlock base n (base + i) = true :=
        (stepInBlock_iff base n (base + i)).mpr ⟨by omega, by omega⟩
      have hSub : base + i - base = i := by omega
      simp [hIn, hSub]
    · rw [hNext j hj, hCh]; rfl

/-- **Exact Guard + Functional Transition Decomposition (`stepOpConstraints_iff_guard_and_next`)**:
    For every valid `StepConstraintKind`, `stepOpConstraints kind c0 x` vanishes if and only if
    its pure pre-state guard list `stepOpGuardResiduals kind c0 x` vanishes AND all 44 `next`
    state limbs equal `stepOpExpectedNext kind c0 x j`. -/
theorem stepOpConstraints_iff_guard_and_next (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (hValid : kind.validSlot = true) :
    allZeroGoldilocks (stepOpConstraints kind c0 x) = true ↔
      allZeroGoldilocks (stepOpGuardResiduals kind c0 x) = true ∧
      ∀ j < 44, x.next j = stepOpExpectedNext kind c0 x j := by
  have hSingle : ∀ r : Goldilocks, allZeroGoldilocks [r] = (r == Goldilocks.zero) := by
    intro r; simp [allZeroGoldilocks_eq]
  have hPair : ∀ r0 r1 : Goldilocks,
      allZeroGoldilocks [r0, r1] = ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero)) := by
    intros; simp [allZeroGoldilocks_eq]
  cases kind with
  | idle =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    rw [allZero_map_iff]
    exact ⟨fun h => ⟨by rw [allZeroGoldilocks_eq]; rfl, h⟩, fun h => h.2⟩
  | statefulHmsgBlock0 =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    have hTail5 : ∀ (r0 r1 r2 r3 r4 : Goldilocks),
        allZeroGoldilocks [r0, r1, r2, r3, r4] =
          (allZeroGoldilocks [r0, r1, r2, r3] && (r4 == Goldilocks.zero)) := by
      intros; simp [allZeroGoldilocks_eq, Bool.and_assoc]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_flatMap_triple_iff,
      hTail5, beq_iff_eq, g_sub_eq_zero_iff, allZero_stepNextIsPerm_iff,
      allZero_stepZeroElsewhere_iff]
    constructor
    · rintro ⟨⟨⟨⟨⟨hB6, hB32⟩, hStIn, hRoot⟩, hT4, hKp⟩, hMain⟩, hZero⟩
      refine ⟨⟨⟨⟨hB6, hB32⟩, hStIn⟩, hT4⟩, fun j hj => ?_⟩
      by_cases hC : stepInBlock stCurRoot 4 j = true
      · rw [hC]; simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stCurRoot 4 j).mp hC
        have hAdd : stCurRoot + (j - stCurRoot) = j := by simp only [stCurRoot.public_eqs] at *; omega
        simpa only [hAdd] using hRoot (j - stCurRoot) (by simp only [stCurRoot.public_eqs] at *; omega)
      · have hCF : stepInBlock stCurRoot 4 j = false := Bool.eq_false_iff.mpr hC
        rw [hCF]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hK : j = stKpIdx
        · subst hK; simp [hKp]
        · simp only [hK, ↓reduceIte]
          by_cases hM : stepInBlock stMainSponge 12 j = true
          · rw [hM]; simp only [↓reduceIte]
            obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stMainSponge 12 j).mp hM
            have hAdd : stMainSponge + (j - stMainSponge) = j := by omega
            simpa only [hAdd] using hMain (j - stMainSponge) (by simp only [stMainSponge.public_eqs] at *; omega)
          · have hMF : stepInBlock stMainSponge 12 j = false := Bool.eq_false_iff.mpr hM
            rw [hMF]; simp only [Bool.false_eq_true, ↓reduceIte]
            exact hZero j hj (by simp [hCF, beq_false_of_ne hK, hMF])
    · rintro ⟨⟨⟨⟨hB6, hB32⟩, hStIn⟩, hT4⟩, hNext⟩
      refine ⟨⟨⟨⟨⟨hB6, hB32⟩, hStIn, fun i hi => ?_⟩, hT4, ?_⟩, fun i hi => ?_⟩, fun j hj hK => ?_⟩
      · rw [hNext (stCurRoot + i) (by simp only [stCurRoot.public_eqs]; omega)]
        have hC : stepInBlock stCurRoot 4 (stCurRoot + i) = true := by
          simp only [stepInBlock.public_eqs, stCurRoot.public_eqs]; simp; omega
        have hSub : stCurRoot + i - stCurRoot = i := by omega
        rw [hC]; simp only [↓reduceIte, hSub]
      · rw [hNext stKpIdx (by decide)]
        have hCF : stepInBlock stCurRoot 4 stKpIdx = false := by decide
        simp [hCF]
      · rw [hNext (stMainSponge + i) (by simp only [stMainSponge.public_eqs]; omega)]
        have hCF : stepInBlock stCurRoot 4 (stMainSponge + i) = false := by
          simp only [stepInBlock.public_eqs, stCurRoot.public_eqs, stMainSponge.public_eqs]; simp; omega
        have hKNe : stMainSponge + i ≠ stKpIdx := by simp only [stMainSponge.public_eqs, stKpIdx.public_eqs]; omega
        have hMT : stepInBlock stMainSponge 12 (stMainSponge + i) = true := by
          simp only [stepInBlock.public_eqs, stMainSponge.public_eqs]; simp; omega
        have hSub : stMainSponge + i - stMainSponge = i := by omega
        simp [hCF, hKNe, hMT, hSub]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hK
        simp [hK.1.1, hK.1.2, hK.2]
  | statefulHmsgBlock1 | forsRootsSpongeInit | forsRootsPairAbsorb _
  | detTreeHmsgBlock0 | wotsTellInit | wotsTellPairAbsorb _ =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true]
    rw [and_assoc]
    exact and_congr_right' (stepBlockUpdate_iff x stMainSponge 12 (by decide))
  | statefulHmsgSqueeze | detTreeHmsgBlock1 =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_stepNextIsPerm_iff,
      allZero_map_iff, hSingle, beq_iff_eq, allZero_stepCarryUnchanged_iff]
    rw [and_assoc, and_assoc, and_assoc]
    apply and_congr_right'
    constructor
    · rintro ⟨hMain, hRem, hAcc, hCarry⟩ j hj
      by_cases hR : stepInBlock stRemPack 6 j = true
      · rw [hR]; simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stRemPack 6 j).mp hR
        have hAdd : stRemPack + (j - stRemPack) = j := by omega
        simpa only [hAdd] using hRem (j - stRemPack) (by simp only [stRemPack.public_eqs] at *; omega)
      · have hRF : stepInBlock stRemPack 6 j = false := Bool.eq_false_iff.mpr hR
        rw [hRF]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hM : stepInBlock stMainSponge 12 j = true
        · rw [hM]; simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stMainSponge 12 j).mp hM
          have hAdd : stMainSponge + (j - stMainSponge) = j := by omega
          simpa only [hAdd] using hMain (j - stMainSponge) (by simp only [stMainSponge.public_eqs] at *; omega)
        · have hMF : stepInBlock stMainSponge 12 j = false := Bool.eq_false_iff.mpr hM
          rw [hMF]; simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hA : j = stAccOrU1
          · subst hA; simp [hAcc]
          · simp only [hA, ↓reduceIte]
            exact hCarry j hj (by simp [hRF, hMF, beq_false_of_ne hA])
    · intro hNext
      refine ⟨fun i hi => ?_, fun s hs => ?_, ?_, fun j hj hCh => ?_⟩
      · rw [hNext (stMainSponge + i) (by simp only [stMainSponge.public_eqs]; omega)]
        have hRF : stepInBlock stRemPack 6 (stMainSponge + i) = false := by
          simp only [stepInBlock.public_eqs, stRemPack.public_eqs, stMainSponge.public_eqs]; simp
        have hMT : stepInBlock stMainSponge 12 (stMainSponge + i) = true := by
          simp only [stepInBlock.public_eqs, stMainSponge.public_eqs]; simp; omega
        have hSub : stMainSponge + i - stMainSponge = i := by omega
        simp [hRF, hMT, hSub]
      · rw [hNext (stRemPack + s) (by simp only [stRemPack.public_eqs]; omega)]
        have hRT : stepInBlock stRemPack 6 (stRemPack + s) = true := by
          simp only [stepInBlock.public_eqs, stRemPack.public_eqs]; simp; omega
        simp [hRT]
      · rw [hNext stAccOrU1 (by decide)]
        have hRF : stepInBlock stRemPack 6 stAccOrU1 = false := by decide
        have hMF : stepInBlock stMainSponge 12 stAccOrU1 = false := by decide
        simp [hRF, hMF]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
        simp [hCh.1.1, hCh.1.2, hCh.2]
  | statelessDeriveBlock0 =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_stepNextIsPerm_iff,
      allZero_stepZeroElsewhere_iff]
    rw [and_assoc]
    apply and_congr_right'
    constructor
    · rintro ⟨hMain, hZero⟩ j hj
      cases hM : stepInBlock stMainSponge 12 j
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hZero j hj hM
      · simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stMainSponge 12 j).mp hM
        have hAdd : stMainSponge + (j - stMainSponge) = j := by omega
        simpa only [hAdd] using hMain (j - stMainSponge) (by simp only [stMainSponge.public_eqs] at *; omega)
    · intro hNext
      refine ⟨fun i hi => ?_, fun j hj hM => ?_⟩
      · rw [hNext (stMainSponge + i) (by simp only [stMainSponge.public_eqs]; omega)]
        have hMT : stepInBlock stMainSponge 12 (stMainSponge + i) = true := by
          simp only [stepInBlock.public_eqs, stMainSponge.public_eqs]; simp; omega
        have hSub : stMainSponge + i - stMainSponge = i := by omega
        simp [hMT, hSub]
      · rw [hNext j hj, hM]; rfl
  | statelessDeriveBlock1 =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_stepNextIsPerm_iff,
      allZero_map_iff, allZero_stepCarryUnchanged_iff]
    rw [and_assoc, and_assoc]
    apply and_congr_right'
    constructor
    · rintro ⟨hMain, hRem, hCarry⟩ j hj
      by_cases hM : stepInBlock stMainSponge 12 j = true
      · rw [hM]; simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stMainSponge 12 j).mp hM
        have hAdd : stMainSponge + (j - stMainSponge) = j := by omega
        simpa only [hAdd] using hMain (j - stMainSponge) (by simp only [stMainSponge.public_eqs] at *; omega)
      · have hMF : stepInBlock stMainSponge 12 j = false := Bool.eq_false_iff.mpr hM
        rw [hMF]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hR : stepInBlock stRemPack 6 j = true
        · rw [hR]; simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stRemPack 6 j).mp hR
          have hAdd : stRemPack + (j - stRemPack) = j := by omega
          simpa only [hAdd] using hRem (j - stRemPack) (by simp only [stRemPack.public_eqs] at *; omega)
        · have hRF : stepInBlock stRemPack 6 j = false := Bool.eq_false_iff.mpr hR
          rw [hRF]; simp only [Bool.false_eq_true, ↓reduceIte]
          exact hCarry j hj (by simp [hMF, hRF])
    · intro hNext
      refine ⟨fun i hi => ?_, fun s hs => ?_, fun j hj hCh => ?_⟩
      · rw [hNext (stMainSponge + i) (by simp only [stMainSponge.public_eqs]; omega)]
        have hMT : stepInBlock stMainSponge 12 (stMainSponge + i) = true := by
          simp only [stepInBlock.public_eqs, stMainSponge.public_eqs]; simp; omega
        have hSub : stMainSponge + i - stMainSponge = i := by omega
        simp [hMT, hSub]
      · rw [hNext (stRemPack + s) (by simp only [stRemPack.public_eqs]; omega)]
        have hMF : stepInBlock stMainSponge 12 (stRemPack + s) = false := by
          simp only [stepInBlock.public_eqs, stRemPack.public_eqs, stMainSponge.public_eqs]; simp; omega
        have hRT : stepInBlock stRemPack 6 (stRemPack + s) = true := by
          simp only [stepInBlock.public_eqs, stRemPack.public_eqs]; simp; omega
        simp [hMF, hRT]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff] at hCh
        simp [hCh.1, hCh.2]
  | statelessDecompLimb l =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_map_iff, g_sub_eq_zero_iff]
  | forsLeafHash slot =>
    have hSlotLt : slot < 6 := by simpa [StepConstraintKind.validSlot.public_eqs] using hValid
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    have hTail5 : ∀ (r0 r1 r2 r3 r4 : Goldilocks),
        allZeroGoldilocks [r0, r1, r2, r3, r4] =
          (allZeroGoldilocks [r0, r1, r2, r3] && (r4 == Goldilocks.zero)) := by
      intros; simp [allZeroGoldilocks_eq, Bool.and_assoc]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, hSingle, hPair, hTail5,
      allZero_flatMap_triple_iff, beq_iff_eq, g_sub_eq_zero_iff,
      allZero_stepCarryUnchanged_iff]
    constructor
    · rintro ⟨⟨⟨⟨hQ, hPack, hNextPack⟩, hIn, hNextWk⟩, hT4, hNextCur⟩, hCarry⟩
      refine ⟨⟨⟨⟨hQ, hPack⟩, hIn⟩, hT4⟩, fun j hj => ?_⟩
      by_cases hP : j = stRemPack + slot
      · subst hP; simp [hNextPack]
      · simp only [hP, ↓reduceIte]
        by_cases hW : stepInBlock stWork 4 j = true
        · rw [hW]; simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hW
          have hAdd : stWork + (j - stWork) = j := by omega
          simpa only [hAdd] using hNextWk (j - stWork) (by simp only [stWork.public_eqs] at *; omega)
        · have hWF : stepInBlock stWork 4 j = false := Bool.eq_false_iff.mpr hW
          rw [hWF]; simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hC : j = stCursorIdx
          · subst hC; simp [hNextCur]
          · simp only [hC, ↓reduceIte]
            exact hCarry j hj (by simp [beq_false_of_ne hP, hWF, beq_false_of_ne hC])
    · rintro ⟨⟨⟨⟨hQ, hPack⟩, hIn⟩, hT4⟩, hNext⟩
      refine ⟨⟨⟨⟨hQ, hPack, ?_⟩, hIn, fun i hi => ?_⟩, hT4, ?_⟩, fun j hj hCh => ?_⟩
      · rw [hNext (stRemPack + slot) (by simp only [stRemPack.public_eqs]; omega)]; simp
      · rw [hNext (stWork + i) (by simp only [stWork.public_eqs]; omega)]
        have hPNe : stWork + i ≠ stRemPack + slot := by simp only [stWork.public_eqs, stRemPack.public_eqs]; omega
        have hWT : stepInBlock stWork 4 (stWork + i) = true := by
          simp only [stepInBlock.public_eqs, stWork.public_eqs]; simp; omega
        have hSub : stWork + i - stWork = i := by omega
        simp [hPNe, hWT, hSub]
      · rw [hNext stCursorIdx (by decide)]
        have hPNe : stCursorIdx ≠ stRemPack + slot := by simp only [stCursorIdx.public_eqs, stRemPack.public_eqs]; omega
        have hWF : stepInBlock stWork 4 stCursorIdx = false := by decide
        simp [hPNe, hWF]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
        simp [hCh.1.1, hCh.1.2, hCh.2]
  | forsMerkleBlockA =>
    simpa only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext] using stepMerkleBlockA_iff x domainForsNode ((c0 +ₚ (x.prev stKpIdx *ₚ ‹2 ^ 16›)) +ₚ x.aux 1)
  | forsMerkleBlockB isTreeLast isOddTree =>
    cases isTreeLast <;> cases isOddTree
    · simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
      simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte, List.append_nil,
        allZeroGoldilocks_append, Bool.and_eq_true]
      exact and_congr_right' (stepBlockUpdate_iff x stWork 4 (by decide))
    · simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
      simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte, List.append_nil,
        allZeroGoldilocks_append, Bool.and_eq_true]
      exact and_congr_right' (stepBlockUpdate_iff x stWork 4 (by decide))
    · have hSplit :
          stepOpConstraints (.forsMerkleBlockB true false) c0 x =
            stepOpGuardResiduals (.forsMerkleBlockB true false) c0 x ++
            (stepNextIsPerm x stCurRoot 4 ++
             stepCarryUnchanged x (fun j => stepInBlock stCurRoot 4 j)) := by
        simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals,
          Bool.not_false, Bool.and_self, ↓reduceIte, List.append_assoc]
      rw [hSplit, allZeroGoldilocks_append, Bool.and_eq_true]
      unfold stepOpExpectedNext
      simp only [Bool.not_false, Bool.and_self, ↓reduceIte,
        allZeroGoldilocks_append, Bool.and_eq_true]
      exact and_congr_right' (stepBlockUpdate_iff x stCurRoot 4 (by decide))
    · have hSplit :
          stepOpConstraints (.forsMerkleBlockB true true) c0 x =
            stepOpGuardResiduals (.forsMerkleBlockB true true) c0 x ++
            (stepNextIsPerm x stWork 4 ++
             stepCarryUnchanged x (fun j => stepInBlock stWork 4 j)) := by
        simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals,
          Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
      rw [hSplit, allZeroGoldilocks_append, Bool.and_eq_true]
      unfold stepOpExpectedNext
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        allZeroGoldilocks_append, Bool.and_eq_true]
      exact and_congr_right' (stepBlockUpdate_iff x stWork 4 (by decide))
  | forsRootsFinalSqueeze =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true]
    rw [and_assoc]
    exact and_congr_right' (stepBlockUpdate_iff x stCurRoot 4 (by decide))
  | hmsgDecompLimb l =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_map_iff, g_sub_eq_zero_iff]
  | wotsChainStep0 slot =>
    have hSlotLt : slot < 5 := by simpa [StepConstraintKind.validSlot.public_eqs] using hValid
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    have hHead7 : ∀ (r0 r1 r2 r3 r4 r5 r6 : Goldilocks),
        allZeroGoldilocks [r0, r1, r2, r3, r4, r5, r6] =
          (allZeroGoldilocks [r0, r1, r2, r3, r4, r5] && (r6 == Goldilocks.zero)) := by
      intros; simp [allZeroGoldilocks_eq, Bool.and_assoc]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, hHead7, hPair,
      allZero_flatMap_triple_iff, beq_iff_eq, g_sub_eq_zero_iff,
      allZero_stepCarryUnchanged_iff]
    constructor
    · rintro ⟨⟨⟨⟨⟨hU, hNextPack⟩, hIn, hNextWk⟩, hStepIn⟩, hNextU1, hNextU2⟩, hCarry⟩
      refine ⟨⟨⟨hU, hIn⟩, hStepIn⟩, fun j hj => ?_⟩
      by_cases hP : j = stRemPack + slot
      · subst hP; simp [hNextPack]
      · simp only [hP, ↓reduceIte]
        by_cases hW : stepInBlock stWork 4 j = true
        · rw [hW]; simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hW
          have hAdd : stWork + (j - stWork) = j := by omega
          simpa only [hAdd] using hNextWk (j - stWork) (by simp only [stWork.public_eqs] at *; omega)
        · have hWF : stepInBlock stWork 4 j = false := Bool.eq_false_iff.mpr hW
          rw [hWF]; simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hU1 : j = stAccOrU1
          · subst hU1; simp [hNextU1]
          · simp only [hU1, ↓reduceIte]
            by_cases hU2 : j = stWotsU2
            · subst hU2; simp [hNextU2]
            · simp only [hU2, ↓reduceIte]
              exact hCarry j hj
                (by simp [beq_false_of_ne hP, hWF, beq_false_of_ne hU1, beq_false_of_ne hU2])
    · rintro ⟨⟨⟨hU, hIn⟩, hStepIn⟩, hNext⟩
      refine ⟨⟨⟨⟨⟨hU, ?_⟩, hIn, fun i hi => ?_⟩, hStepIn⟩, ?_, ?_⟩, fun j hj hCh => ?_⟩
      · rw [hNext (stRemPack + slot) (by simp only [stRemPack.public_eqs]; omega)]; simp
      · rw [hNext (stWork + i) (by simp only [stWork.public_eqs]; omega)]
        have hPNe : stWork + i ≠ stRemPack + slot := by simp only [stWork.public_eqs, stRemPack.public_eqs]; omega
        have hWT : stepInBlock stWork 4 (stWork + i) = true := by
          simp only [stepInBlock.public_eqs, stWork.public_eqs]; simp; omega
        have hSub : stWork + i - stWork = i := by omega
        simp [hPNe, hWT, hSub]
      · rw [hNext stAccOrU1 (by decide)]
        have hPNe : stAccOrU1 ≠ stRemPack + slot := by simp only [stAccOrU1.public_eqs, stRemPack.public_eqs]; omega
        have hWF : stepInBlock stWork 4 stAccOrU1 = false := by decide
        simp [hPNe, hWF]
      · rw [hNext stWotsU2 (by decide)]
        have hPNe : stWotsU2 ≠ stRemPack + slot := by simp only [stWotsU2.public_eqs, stRemPack.public_eqs]; omega
        have hWF : stepInBlock stWork 4 stWotsU2 = false := by decide
        have hU1Ne : stWotsU2 ≠ stAccOrU1 := by decide
        simp [hPNe, hWF, hU1Ne]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
        simp [hCh.1.1.1, hCh.1.1.2, hCh.1.2, hCh.2]
  | wotsChainStep1 =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_flatMap_triple_iff,
      g_sub_eq_zero_iff, allZero_stepCarryUnchanged_iff]
    constructor
    · rintro ⟨⟨⟨hIn, hNextWk⟩, hStepIn⟩, hCarry⟩
      refine ⟨⟨hIn, hStepIn⟩, fun j hj => ?_⟩
      cases hW : stepInBlock stWork 4 j
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hCarry j hj hW
      · simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hW
        have hAdd : stWork + (j - stWork) = j := by omega
        simpa only [hAdd] using hNextWk (j - stWork) (by simp only [stWork.public_eqs] at *; omega)
    · rintro ⟨⟨hIn, hStepIn⟩, hNext⟩
      refine ⟨⟨⟨hIn, fun i hi => ?_⟩, hStepIn⟩, fun j hj hCh => ?_⟩
      · rw [hNext (stWork + i) (by simp only [stWork.public_eqs]; omega)]
        have hWT : stepInBlock stWork 4 (stWork + i) = true := by
          simp only [stepInBlock.public_eqs, stWork.public_eqs]; simp; omega
        have hSub : stWork + i - stWork = i := by omega
        simp [hWT, hSub]
      · rw [hNext j hj, hCh]; rfl
  | wotsChainStep2 isOdd =>
    cases isOdd
    · simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
      simp only [Bool.false_eq_true, ↓reduceIte, allZeroGoldilocks_append, Bool.and_eq_true,
        allZero_flatMap_triple_iff, g_sub_eq_zero_iff, allZero_stepCarryUnchanged_iff]
      constructor
      · rintro ⟨⟨⟨hIn, hNextB⟩, hStepIn⟩, hCarry⟩
        refine ⟨⟨hIn, hStepIn⟩, fun j hj => ?_⟩
        cases hB : stepInBlock stSubSponge 4 j
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact hCarry j hj hB
        · simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stSubSponge 4 j).mp hB
          have hAdd : stSubSponge + (j - stSubSponge) = j := by omega
          simpa only [hAdd] using hNextB (j - stSubSponge) (by simp only [stSubSponge.public_eqs] at *; omega)
      · rintro ⟨⟨hIn, hStepIn⟩, hNext⟩
        refine ⟨⟨⟨hIn, fun i hi => ?_⟩, hStepIn⟩, fun j hj hCh => ?_⟩
        · rw [hNext (stSubSponge + i) (by simp only [stSubSponge.public_eqs]; omega)]
          have hBT : stepInBlock stSubSponge 4 (stSubSponge + i) = true := by
            simp only [stepInBlock.public_eqs, stSubSponge.public_eqs]; simp; omega
          have hSub : stSubSponge + i - stSubSponge = i := by omega
          simp [hBT, hSub]
        · rw [hNext j hj, hCh]; rfl
    · simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
      simp only [↓reduceIte, allZeroGoldilocks_append, Bool.and_eq_true,
        allZero_flatMap_triple_iff, g_sub_eq_zero_iff, allZero_stepCarryUnchanged_iff]
      constructor
      · rintro ⟨⟨⟨hIn, hNextB⟩, hStepIn⟩, hCarry⟩
        refine ⟨⟨hIn, hStepIn⟩, fun j hj => ?_⟩
        cases hB : stepInBlock stWork 4 j
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact hCarry j hj hB
        · simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hB
          have hAdd : stWork + (j - stWork) = j := by omega
          simpa only [hAdd] using hNextB (j - stWork) (by simp only [stWork.public_eqs] at *; omega)
      · rintro ⟨⟨hIn, hStepIn⟩, hNext⟩
        refine ⟨⟨⟨hIn, fun i hi => ?_⟩, hStepIn⟩, fun j hj hCh => ?_⟩
        · rw [hNext (stWork + i) (by simp only [stWork.public_eqs]; omega)]
          have hBT : stepInBlock stWork 4 (stWork + i) = true := by
            simp only [stepInBlock.public_eqs, stWork.public_eqs]; simp; omega
          have hSub : stWork + i - stWork = i := by omega
          simp [hBT, hSub]
        · rw [hNext j hj, hCh]; rfl
  | wotsTellFinalSqueeze =>
    simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_stepNextIsPerm_iff,
      hSingle, beq_iff_eq, g_sub_eq_zero_iff, allZero_stepCarryUnchanged_iff]
    rw [and_assoc, and_assoc]
    apply and_congr_right'
    constructor
    · rintro ⟨hWk, hCur, hCarry⟩ j hj
      by_cases hW : stepInBlock stWork 4 j = true
      · rw [hW]; simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hW
        have hAdd : stWork + (j - stWork) = j := by omega
        simpa only [hAdd] using hWk (j - stWork) (by simp only [stWork.public_eqs] at *; omega)
      · have hWF : stepInBlock stWork 4 j = false := Bool.eq_false_iff.mpr hW
        rw [hWF]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hC : j = stCursorIdx
        · subst hC; simp [hCur]
        · simp only [hC, ↓reduceIte]
          exact hCarry j hj (by simp [hWF, beq_false_of_ne hC])
    · intro hNext
      refine ⟨fun i hi => ?_, ?_, fun j hj hCh => ?_⟩
      · rw [hNext (stWork + i) (by simp only [stWork.public_eqs]; omega)]
        have hWT : stepInBlock stWork 4 (stWork + i) = true := by
          simp only [stepInBlock.public_eqs, stWork.public_eqs]; simp; omega
        have hSub : stWork + i - stWork = i := by omega
        simp [hWT, hSub]
      · rw [hNext stCursorIdx (by decide)]
        have hWF : stepInBlock stWork 4 stCursorIdx = false := by decide
        simp [hWF]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
        simp [hCh.1, hCh.2]
  | xmssMerkleBlockA =>
    simpa only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext] using stepMerkleBlockA_iff x domainMerkleNode (c0 +ₚ x.aux 1)
  | xmssMerkleBlockB isLayerLast isTopFinal =>
    cases isLayerLast
    · simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals, stepOpExpectedNext]
      simp only [Bool.not_false, ↓reduceIte, List.append_nil,
        allZeroGoldilocks_append, Bool.and_eq_true]
      exact and_congr_right' (stepBlockUpdate_iff x stWork 4 (by decide))
    · cases isTopFinal
      · -- `isLayerLast = true, isTopFinal = false`
        have hSplitList :
            stepOpConstraints (.xmssMerkleBlockB true false) c0 x =
              stepOpGuardResiduals (.xmssMerkleBlockB true false) c0 x ++
              (stepNextIsPerm x stCurRoot 4 ++
               [x.next stKpIdx -ₚ stepWeightedSum x.aux (fun i => 2 ^ i) 4,
                x.next stTreeLo -ₚ
                  (stepWeightedSum (fun i => x.aux (4 + i)) (fun i => 4 ^ i) 14 +ₚ
                    (stepWeightedSum (fun i => x.aux (18 + i)) (fun i => 4 ^ i) 2 *ₚ ‹2 ^ 28›)),
                x.next stTreeHi -ₚ stepWeightedSum (fun i => x.aux (20 + i)) (fun i => 4 ^ i) 14] ++
               stepCarryUnchanged x
                 (fun j => stepInBlock stCurRoot 4 j || j == stKpIdx || j == stTreeLo || j == stTreeHi)) := by
          simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
        rw [hSplitList, allZeroGoldilocks_append, Bool.and_eq_true]
        apply and_congr_right'
        unfold stepOpExpectedNext
        have hTriple : ∀ (r0 r1 r2 : Goldilocks),
            allZeroGoldilocks [r0, r1, r2] =
              ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero) && (r2 == Goldilocks.zero)) := by
          intros; simp [allZeroGoldilocks_eq, Bool.and_assoc]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, allZeroGoldilocks_append,
          Bool.and_eq_true, allZero_stepNextIsPerm_iff, hTriple, beq_iff_eq,
          g_sub_eq_zero_iff, allZero_stepCarryUnchanged_iff]
        constructor
        · rintro ⟨⟨hCur, ⟨hKp, hLo⟩, hHi⟩, hCarry⟩ j hj
          by_cases hC : stepInBlock stCurRoot 4 j = true
          · rw [hC]; simp only [↓reduceIte]
            obtain ⟨hLoB, hHiB⟩ := (stepInBlock_iff stCurRoot 4 j).mp hC
            have hAdd : stCurRoot + (j - stCurRoot) = j := by omega
            simpa only [hAdd] using hCur (j - stCurRoot) (by simp only [stCurRoot.public_eqs] at *; omega)
          · have hCF : stepInBlock stCurRoot 4 j = false := Bool.eq_false_iff.mpr hC
            rw [hCF]; simp only [Bool.false_eq_true, ↓reduceIte]
            by_cases hK : j = stKpIdx
            · subst hK; simp [hKp]
            · simp only [hK, ↓reduceIte]
              by_cases hTL : j = stTreeLo
              · subst hTL; simp [hLo]
              · simp only [hTL, ↓reduceIte]
                by_cases hTH : j = stTreeHi
                · subst hTH; simp [hHi]
                · simp only [hTH, ↓reduceIte]
                  exact hCarry j hj
                    (by simp [hCF, beq_false_of_ne hK, beq_false_of_ne hTL, beq_false_of_ne hTH])
        · intro hNext
          refine ⟨⟨fun i hi => ?_, ⟨?_, ?_⟩, ?_⟩, fun j hj hCh => ?_⟩
          · rw [hNext (stCurRoot + i) (by simp only [stCurRoot.public_eqs]; omega)]
            have hCT : stepInBlock stCurRoot 4 (stCurRoot + i) = true := by
              simp only [stepInBlock.public_eqs, stCurRoot.public_eqs]; simp; omega
            have hSub : stCurRoot + i - stCurRoot = i := by omega
            rw [hCT]; simp only [↓reduceIte, hSub]
          · rw [hNext stKpIdx (by decide)]
            have hCF : stepInBlock stCurRoot 4 stKpIdx = false := by decide
            simp [hCF]
          · rw [hNext stTreeLo (by decide)]
            have hCF : stepInBlock stCurRoot 4 stTreeLo = false := by decide
            have hKNe : stTreeLo ≠ stKpIdx := by decide
            simp [hCF, hKNe]
          · rw [hNext stTreeHi (by decide)]
            have hCF : stepInBlock stCurRoot 4 stTreeHi = false := by decide
            have hKNe : stTreeHi ≠ stKpIdx := by decide
            have hTLNe : stTreeHi ≠ stTreeLo := by decide
            simp [hCF, hKNe, hTLNe]
          · rw [hNext j hj]
            simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
            simp [hCh.1.1.1, hCh.1.1.2, hCh.1.2, hCh.2]
      · -- `isLayerLast = true, isTopFinal = true`
        have hSplitList :
            stepOpConstraints (.xmssMerkleBlockB true true) c0 x =
              stepOpGuardResiduals (.xmssMerkleBlockB true true) c0 x ++
              (List.range 44).map x.next := by
          simp only [stepOpConstraints.public_eqs, stepOpGuardResiduals,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
        rw [hSplitList, allZeroGoldilocks_append, Bool.and_eq_true]
        apply and_congr_right'
        unfold stepOpExpectedNext
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, allZero_map_iff]

/-- Selector-explicit 256-column `Hem` AIR row: pairs a `StepOpRow` (`256` witness columns)
    with explicit field-valued `StepOp` selectors `sels` (`52` selectors over `allStepConstraintKinds`). -/

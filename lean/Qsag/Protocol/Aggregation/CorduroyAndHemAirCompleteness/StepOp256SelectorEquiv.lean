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
structure HemStepOpSelectorRow where
  row  : StepOpRow
  sels : List Goldilocks
  deriving DecidableEq, Repr

/-- Index of a `StepConstraintKind` inside `allStepConstraintKinds`. -/
def stepConstraintKindIdx (kind : StepConstraintKind) : Nat :=
  allStepConstraintKinds.idxOf kind

/-- Canonical one-hot selector vector for `kind` over `allStepConstraintKinds`. -/
def oneHotStepSelectors (kind : StepConstraintKind) : List Goldilocks :=
  allStepConstraintKinds.map fun k => if k == kind then Goldilocks.one else Goldilocks.zero

/-- Selector booleanity residuals `s_k * (1 - s_k)` for all `k < allStepConstraintKinds.length`. -/
def hemStepSelectorBoolResiduals (sels : List Goldilocks) : List Goldilocks :=
  (List.range allStepConstraintKinds.length).map fun k =>
    stepBoolCheck (sels.getD k Goldilocks.zero)

/-- Selector pairwise-orthogonality residuals `s_i * s_j` for all `0 ≤ i < j < allStepConstraintKinds.length`. -/
def hemStepSelectorOrthResiduals (sels : List Goldilocks) : List Goldilocks :=
  (List.range allStepConstraintKinds.length).flatMap fun i =>
    (List.range i).map fun j =>
      sels.getD j Goldilocks.zero *ₚ sels.getD i Goldilocks.zero

/-- Scheduled opcode pin residuals:
    - On an inactive slot (`none`), every selector is pinned to `0`.
    - On an active slot (`some _`), the scheduled selector `s_{uid_t}` is pinned to `1`. -/
def hemStepSchedulePinResiduals (profile : AggSigProfile) (slot : StepOpSlot) (t : Nat)
    (sels : List Goldilocks) : List Goldilocks :=
  match slot with
  | none =>
    (List.range allStepConstraintKinds.length).map fun k => sels.getD k Goldilocks.zero
  | some _ =>
    let kind := (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1
    [Goldilocks.one -ₚ sels.getD (stepConstraintKindIdx kind) Goldilocks.zero]

/-- Selector-muxed opcode guard & next-state transition residuals on row `t`:
    - Each `kind_k`'s pure pre-state guard list is gated by `s_k * g = 0`.
    - On an active slot, each `next` limb satisfies `x.next j = Σ_k s_k * stepOpExpectedNext kind_k c0 x j`. -/
def hemStepMuxedInputResiduals (c0 : Goldilocks) (x : StepOpRowInputs)
    (sels : List Goldilocks) : List Goldilocks :=
  let guardRes :=
    (List.range allStepConstraintKinds.length).flatMap fun k =>
      let sk := sels.getD k Goldilocks.zero
      let kind := allStepConstraintKinds.getD k .idle
      (stepOpGuardResiduals kind c0 x).map (fun g => sk *ₚ g)
  let nextRes :=
    (List.range 44).map fun j =>
      x.next j -ₚ
        (List.range allStepConstraintKinds.length).foldl
          (fun acc k =>
            acc +ₚ (sels.getD k Goldilocks.zero *ₚ
              stepOpExpectedNext (allStepConstraintKinds.getD k .idle) c0 x j))
          Goldilocks.zero
  guardRes ++ nextRes

/-- Read the shared mux evaluator's inputs from the committed row. -/
def hemStepMuxedOpResiduals (slot : StepOpSlot) (c0 : Goldilocks) (row : StepOpRow)
    (sels : List Goldilocks) : List Goldilocks :=
  match slot with
  | none => []
  | some pub => hemStepMuxedInputResiduals c0 (stepOpRowInputs pub row) sels

/-- Full intra-row residuals of a selector-explicit `HemStepOpSelectorRow` (including `s_i * s_j = 0`). -/
def hemStepSelectorRowResiduals (profile : AggSigProfile) (slot : StepOpSlot) (t : Nat)
    (sr : HemStepOpSelectorRow) : List Goldilocks :=
  let c0 := Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).2
  (stepOpPermTrace sr.row).2 ++
  stepOpBoundaryResiduals (stepOpRowsPerSigner profile) t sr.row ++
  hemStepSelectorBoolResiduals sr.sels ++
  hemStepSelectorOrthResiduals sr.sels ++
  hemStepSchedulePinResiduals profile slot t sr.sels ++
  hemStepMuxedOpResiduals slot c0 sr.row sr.sels

/-- Mutated intra-row residuals omitting ONLY pairwise selector orthogonality `s_i * s_j = 0` (for `#tooth`). -/
def hemStepSelectorRowResidualsOmitOrthogonality (profile : AggSigProfile) (slot : StepOpSlot)
    (t : Nat) (sr : HemStepOpSelectorRow) : List Goldilocks :=
  let c0 := Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).2
  (stepOpPermTrace sr.row).2 ++
  stepOpBoundaryResiduals (stepOpRowsPerSigner profile) t sr.row ++
  hemStepSelectorBoolResiduals sr.sels ++
  hemStepSchedulePinResiduals profile slot t sr.sels ++
  hemStepMuxedOpResiduals slot c0 sr.row sr.sels

def hemStepSelectorIntraFrom (profile : AggSigProfile) (slots : List StepOpSlot) :
    Nat → List HemStepOpSelectorRow → List Goldilocks
  | _, [] => []
  | g, sr :: rest =>
    hemStepSelectorRowResiduals profile (slots.getD (g / stepOpRowsPerSigner profile) none)
      (g % stepOpRowsPerSigner profile) sr ++
    hemStepSelectorIntraFrom profile slots (g + 1) rest

def hemStepSelectorIntraOmitOrthFrom (profile : AggSigProfile) (slots : List StepOpSlot) :
    Nat → List HemStepOpSelectorRow → List Goldilocks
  | _, [] => []
  | g, sr :: rest =>
    hemStepSelectorRowResidualsOmitOrthogonality profile
      (slots.getD (g / stepOpRowsPerSigner profile) none)
      (g % stepOpRowsPerSigner profile) sr ++
    hemStepSelectorIntraOmitOrthFrom profile slots (g + 1) rest

/-- Full selector-explicit 256-column `Hem` AIR validity predicate. -/
def hemStepTraceValid (profile : AggSigProfile) (slots : List StepOpSlot)
    (srows : List HemStepOpSelectorRow) : Bool :=
  decide (0 < slots.length) &&
  decide (srows.length = slots.length * stepOpRowsPerSigner profile) &&
  srows.all (fun sr => sr.row.wellShaped && decide (sr.sels.length = allStepConstraintKinds.length)) &&
  allZeroGoldilocks (hemStepSelectorIntraFrom profile slots 0 srows) &&
  allZeroGoldilocks (stepOp256ShiftResiduals (srows.map HemStepOpSelectorRow.row))

/-- Mutated selector-explicit 256-column `Hem` AIR validity predicate omitting ONLY `s_i * s_j = 0`. -/
def hemStepTraceValidOmitOrthogonality (profile : AggSigProfile) (slots : List StepOpSlot)
    (srows : List HemStepOpSelectorRow) : Bool :=
  decide (0 < slots.length) &&
  decide (srows.length = slots.length * stepOpRowsPerSigner profile) &&
  srows.all (fun sr => sr.row.wellShaped && decide (sr.sels.length = allStepConstraintKinds.length)) &&
  allZeroGoldilocks (hemStepSelectorIntraOmitOrthFrom profile slots 0 srows) &&
  allZeroGoldilocks (stepOp256ShiftResiduals (srows.map HemStepOpSelectorRow.row))

/-- Attach canonical scheduled selectors to a `StepOpRow` table. -/
def attachHonestStepSelectorsFrom (profile : AggSigProfile) (slots : List StepOpSlot) :
    Nat → List StepOpRow → List HemStepOpSelectorRow
  | _, [] => []
  | g, row :: rest =>
    let slot := slots.getD (g / stepOpRowsPerSigner profile) none
    let t := g % stepOpRowsPerSigner profile
    let sels := match slot with
      | none => List.replicate allStepConstraintKinds.length Goldilocks.zero
      | some _ =>
        oneHotStepSelectors (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1
    { row := row, sels := sels } :: attachHonestStepSelectorsFrom profile slots (g + 1) rest

def attachHonestStepSelectors (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) : List HemStepOpSelectorRow :=
  attachHonestStepSelectorsFrom profile slots 0 rows

private theorem allZero_orth_iff (sels : List Goldilocks) :
    allZeroGoldilocks (hemStepSelectorOrthResiduals sels) = true ↔
      ∀ i j, j < i → i < allStepConstraintKinds.length →
        sels.getD j Goldilocks.zero *ₚ sels.getD i Goldilocks.zero = Goldilocks.zero := by
  simp only [hemStepSelectorOrthResiduals, allZeroGoldilocks_eq]
  simp only [List.all_flatMap, List.all_map, List.all_eq_true, List.mem_range,
    Function.comp_apply, beq_iff_eq]
  exact ⟨fun h i j hji hi => h i hi j hji, fun h i hi j hji => h i j hji hi⟩

private theorem nodup_getElem_inj {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      xs[i]'hi = xs[j]'hj → i = j
  | [], _, i, _, hi, _, _ => False.elim (Nat.not_lt_zero i hi)
  | x :: xs, hNd, 0, 0, _, _, _ => rfl
  | x :: xs, hNd, 0, j + 1, _, hj, hEq => by
    obtain ⟨hNotMem, _⟩ := List.nodup_cons.mp hNd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
    exact False.elim (hNotMem (hEq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)))
  | x :: xs, hNd, i + 1, 0, hi, _, hEq => by
    obtain ⟨hNotMem, _⟩ := List.nodup_cons.mp hNd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
    exact False.elim (hNotMem (hEq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)))
  | x :: xs, hNd, i + 1, j + 1, hi, hj, hEq => by
    obtain ⟨_, hNdTail⟩ := List.nodup_cons.mp hNd
    simp only [List.getElem_cons_succ] at hEq
    exact congrArg Nat.succ
      (nodup_getElem_inj hNdTail (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) hEq)

section SelectorEquiv

attribute [local irreducible] stepOpGuardResiduals stepOpExpectedNext

private theorem oneHot_getD_eq (kind : StepConstraintKind) (hMem : kind ∈ allStepConstraintKinds)
    (k : Nat) (hk : k < allStepConstraintKinds.length) :
    (oneHotStepSelectors kind).getD k Goldilocks.zero =
      if k = stepConstraintKindIdx kind then Goldilocks.one else Goldilocks.zero := by
  unfold oneHotStepSelectors stepConstraintKindIdx
  have hkMap : k < (allStepConstraintKinds.map fun x =>
      if x == kind then Goldilocks.one else Goldilocks.zero).length := by simp [hk]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkMap, Option.getD_some, List.getElem_map]
  have hIdxLt : allStepConstraintKinds.idxOf kind < allStepConstraintKinds.length :=
    List.idxOf_lt_length_of_mem hMem
  by_cases hEqIdx : k = allStepConstraintKinds.idxOf kind
  · subst hEqIdx
    have hAt : allStepConstraintKinds[allStepConstraintKinds.idxOf kind]'hIdxLt = kind :=
      List.getElem_idxOf hIdxLt
    simp [hAt]
  · have hNeElem : allStepConstraintKinds[k]'hk ≠ kind := by
      intro hSame
      apply hEqIdx
      have hAt : allStepConstraintKinds[allStepConstraintKinds.idxOf kind]'hIdxLt = kind :=
        List.getElem_idxOf hIdxLt
      exact nodup_getElem_inj allStepConstraintKinds_nodup hk hIdxLt (hSame.trans hAt.symm)
    simp [beq_false_of_ne hNeElem, hEqIdx]

/-- **One-Hot Selector Collapse (`hemStepSelector_oneHot_collapse`)**:
    Under pairwise orthogonality `s_i * s_j = 0` and scheduled pin `1 - s_{uid} = 0`,
    `sels` is forced to equal `oneHotStepSelectors kind`. -/
theorem hemStepSelector_oneHot_collapse (kind : StepConstraintKind) (sels : List Goldilocks)
    (hMem : kind ∈ allStepConstraintKinds)
    (hLen : sels.length = allStepConstraintKinds.length)
    (hOrth : allZeroGoldilocks (hemStepSelectorOrthResiduals sels) = true)
    (hPin : Goldilocks.one -ₚ sels.getD (stepConstraintKindIdx kind) Goldilocks.zero = Goldilocks.zero) :
    sels = oneHotStepSelectors kind := by
  have hOrthFn := (allZero_orth_iff sels).mp hOrth
  have hUidOne : sels.getD (stepConstraintKindIdx kind) Goldilocks.zero = Goldilocks.one :=
    (g_sub_eq_zero_iff.mp hPin).symm
  have hUidLt : stepConstraintKindIdx kind < allStepConstraintKinds.length :=
    List.idxOf_lt_length_of_mem hMem
  apply List.ext_getElem
  · rw [hLen, oneHotStepSelectors, List.length_map]
  · intro k hk1 hk2
    have hkLt : k < allStepConstraintKinds.length := hLen ▸ hk1
    have hLhs : sels[k]'hk1 = sels.getD k Goldilocks.zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1, Option.getD_some]
    have hRhs : (oneHotStepSelectors kind)[k]'hk2 =
        (oneHotStepSelectors kind).getD k Goldilocks.zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2, Option.getD_some]
    rw [hLhs, hRhs, oneHot_getD_eq kind hMem k hkLt]
    by_cases hEq : k = stepConstraintKindIdx kind
    · subst hEq; simpa [List.getD_eq_getElem?_getD] using hUidOne
    · simp only [hEq, ↓reduceIte]
      by_cases hLt : k < stepConstraintKindIdx kind
      · have hProd := hOrthFn (stepConstraintKindIdx kind) k hLt hUidLt
        rw [hUidOne, g_mul_one] at hProd
        exact hProd
      · have hGt : stepConstraintKindIdx kind < k := by omega
        have hProd := hOrthFn k (stepConstraintKindIdx kind) hGt hkLt
        rw [hUidOne, g_one_mul] at hProd
        exact hProd

private theorem foldl_oneHot_sum (n uid : Nat) (hUid : uid < n) (f : Nat → Goldilocks) :
    (List.range n).foldl
      (fun acc k => acc +ₚ ((if k = uid then Goldilocks.one else Goldilocks.zero) *ₚ f k))
      Goldilocks.zero = f uid := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hEq : m = uid
    · subst hEq
      have hZeroPre : ∀ (ls : List Nat), (∀ k ∈ ls, k ≠ m) →
          ls.foldl (fun acc k => acc +ₚ ((if k = m then Goldilocks.one else Goldilocks.zero) *ₚ f k))
            Goldilocks.zero = Goldilocks.zero := by
        intro ls hNe
        induction ls with
        | nil => rfl
        | cons a as ihL =>
          have haNe : a ≠ m := hNe a (List.mem_cons_self ..)
          simp only [List.foldl_cons, haNe, ↓reduceIte, g_zero_mul, g_add_zero]
          exact ihL (fun x hx => hNe x (List.mem_cons_of_mem _ hx))
      rw [hZeroPre (List.range m) (fun k hk => Nat.ne_of_lt (List.mem_range.mp hk))]
      simp only [↓reduceIte, g_one_mul, g_zero_add]
    · have hLtM : uid < m := by omega
      rw [ih hLtM]
      simp only [hEq, ↓reduceIte, g_zero_mul, g_add_zero]

private theorem getD_rep_zero :
    ∀ (n j : Nat), (List.replicate n Goldilocks.zero).getD j Goldilocks.zero = Goldilocks.zero
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, j + 1 => getD_rep_zero n j

private theorem foldl_congr_on {A B : Type} (f g : B → A → B) :
    ∀ (xs : List A) (init : B), (∀ a ∈ xs, ∀ acc, f acc a = g acc a) →
      xs.foldl f init = xs.foldl g init
  | [], _, _ => rfl
  | a :: rest, init, h =>
    (congrArg (fun acc => rest.foldl f acc) (h a (List.mem_cons_self ..) init)).trans
      (foldl_congr_on f g rest (g init a) (fun b hb acc => h b (List.mem_cons_of_mem a hb) acc))

private theorem foldl_selector_sum (n uid : Nat) (hUid : uid < n)
    (sel f : Nat → Goldilocks)
    (hSel : ∀ k < n, sel k = if k = uid then Goldilocks.one else Goldilocks.zero) :
    (List.range n).foldl (fun acc k => acc +ₚ (sel k *ₚ f k)) Goldilocks.zero = f uid := by
  have h := foldl_congr_on
    (fun acc k => acc +ₚ (sel k *ₚ f k))
    (fun acc k => acc +ₚ ((if k = uid then Goldilocks.one else Goldilocks.zero) *ₚ f k))
    (List.range n) Goldilocks.zero
    (fun k hk acc => congrArg (fun v => acc +ₚ (v *ₚ f k)) (hSel k (List.mem_range.mp hk)))
  exact h.trans (foldl_oneHot_sum n uid hUid f)

private theorem hemStep_oneHot_fold (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (hMem : kind ∈ allStepConstraintKinds) (j : Nat) :
    (List.range allStepConstraintKinds.length).foldl
      (fun acc k => acc +ₚ ((oneHotStepSelectors kind).getD k Goldilocks.zero *ₚ
        stepOpExpectedNext (allStepConstraintKinds.getD k .idle) c0 x j))
      Goldilocks.zero = stepOpExpectedNext kind c0 x j := by
  have hUidLt : stepConstraintKindIdx kind < allStepConstraintKinds.length := by
    unfold stepConstraintKindIdx
    exact List.idxOf_lt_length_of_mem hMem
  have hKindAtUid : allStepConstraintKinds.getD (stepConstraintKindIdx kind) .idle = kind := by
    have hIdxLt : allStepConstraintKinds.idxOf kind < allStepConstraintKinds.length :=
      List.idxOf_lt_length_of_mem hMem
    unfold stepConstraintKindIdx
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hIdxLt, Option.getD_some]
    exact List.getElem_idxOf hIdxLt
  have h := foldl_selector_sum allStepConstraintKinds.length (stepConstraintKindIdx kind)
    hUidLt (fun k => (oneHotStepSelectors kind).getD k Goldilocks.zero)
    (fun k => stepOpExpectedNext (allStepConstraintKinds.getD k .idle) c0 x j)
    (oneHot_getD_eq kind hMem)
  exact h.trans (congrArg (fun k => stepOpExpectedNext k c0 x j) hKindAtUid)

private theorem hemStep_oneHot_guards (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (hMem : kind ∈ allStepConstraintKinds) :
    allZeroGoldilocks ((List.range allStepConstraintKinds.length).flatMap fun k =>
      (stepOpGuardResiduals (allStepConstraintKinds.getD k .idle) c0 x).map
        (fun g => (oneHotStepSelectors kind).getD k Goldilocks.zero *ₚ g)) = true ↔
    allZeroGoldilocks (stepOpGuardResiduals kind c0 x) = true := by
  have hUidLt : stepConstraintKindIdx kind < allStepConstraintKinds.length := by
    unfold stepConstraintKindIdx
    exact List.idxOf_lt_length_of_mem hMem
  have hKindAtUid : allStepConstraintKinds.getD (stepConstraintKindIdx kind) .idle = kind := by
    have hIdxLt : allStepConstraintKinds.idxOf kind < allStepConstraintKinds.length :=
      List.idxOf_lt_length_of_mem hMem
    unfold stepConstraintKindIdx
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hIdxLt, Option.getD_some]
    exact List.getElem_idxOf hIdxLt
  constructor
  · intro hGuards
    simp only [allZeroGoldilocks_eq] at hGuards ⊢
    rw [List.all_flatMap, List.all_eq_true] at hGuards
    have hAt := hGuards (stepConstraintKindIdx kind) (List.mem_range.mpr hUidLt)
    rw [oneHot_getD_eq kind hMem _ hUidLt] at hAt
    simp only [↓reduceIte, hKindAtUid, List.all_map] at hAt
    have hComp : ((fun x => x == Goldilocks.zero) ∘ fun g => Goldilocks.one *ₚ g) =
        (fun x => x == Goldilocks.zero) := by
      funext g; simp only [Function.comp, g_one_mul]
    rwa [hComp] at hAt
  · intro hGuardOk
    simp only [allZeroGoldilocks_eq] at hGuardOk ⊢
    rw [List.all_flatMap, List.all_eq_true]
    intro k hkRange
    have hk := List.mem_range.mp hkRange
    rw [oneHot_getD_eq kind hMem k hk, List.all_map]
    by_cases hEq : k = stepConstraintKindIdx kind
    · simp only [hEq, ↓reduceIte, hKindAtUid]
      have hComp : ((fun x => x == Goldilocks.zero) ∘ fun g => Goldilocks.one *ₚ g) =
          (fun x => x == Goldilocks.zero) := by
        funext g; simp only [Function.comp, g_one_mul]
      rwa [hComp]
    · simp only [hEq, ↓reduceIte]
      have hComp0 : ((fun x => x == Goldilocks.zero) ∘ fun g => Goldilocks.zero *ₚ g) =
          (fun _ => true) := by
        funext g; simp only [Function.comp, g_zero_mul, beq_self_eq_true]
      rw [hComp0]
      exact List.all_eq_true.mpr (fun _ _ => rfl)

private theorem hemStep_oneHot_mux (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (hMem : kind ∈ allStepConstraintKinds)
    (hValid : kind.validSlot = true) :
    allZeroGoldilocks (hemStepMuxedInputResiduals c0 x (oneHotStepSelectors kind)) = true ↔
    allZeroGoldilocks (stepOpConstraints kind c0 x) = true := by
  unfold hemStepMuxedInputResiduals
  rw [allZeroGoldilocks_append, Bool.and_eq_true, hemStep_oneHot_guards kind c0 x hMem,
    stepOpConstraints_iff_guard_and_next kind c0 x hValid]
  apply and_congr_right'
  rw [allZero_map_iff]
  constructor
  · intro h j hj
    exact (g_sub_eq_zero_iff.mp (h j hj)).trans (hemStep_oneHot_fold kind c0 x hMem j)
  · intro h j hj
    exact g_sub_eq_zero_iff.mpr ((h j hj).trans (hemStep_oneHot_fold kind c0 x hMem j).symm)

private theorem hemStep_oneHot_selectors (kind : StepConstraintKind)
    (hMem : kind ∈ allStepConstraintKinds) :
    allZeroGoldilocks (hemStepSelectorBoolResiduals (oneHotStepSelectors kind)) = true ∧
    allZeroGoldilocks (hemStepSelectorOrthResiduals (oneHotStepSelectors kind)) = true ∧
    Goldilocks.one -ₚ (oneHotStepSelectors kind).getD (stepConstraintKindIdx kind) Goldilocks.zero =
      Goldilocks.zero := by
  have hUidLt : stepConstraintKindIdx kind < allStepConstraintKinds.length := by
    unfold stepConstraintKindIdx
    exact List.idxOf_lt_length_of_mem hMem
  refine ⟨?_, ?_, ?_⟩
  · unfold hemStepSelectorBoolResiduals
    rw [allZero_map_iff]; intro k hk
    rw [oneHot_getD_eq kind hMem k hk]
    by_cases hEq : k = stepConstraintKindIdx kind
    · simp only [hEq, ↓reduceIte]
      exact (stepBoolCheck_eq_zero_iff _).mpr (.inr rfl)
    · simp only [hEq, ↓reduceIte]
      exact (stepBoolCheck_eq_zero_iff _).mpr (.inl rfl)
  · rw [allZero_orth_iff]; intro i j hji hi
    rw [oneHot_getD_eq kind hMem j (Nat.lt_trans hji hi), oneHot_getD_eq kind hMem i hi]
    by_cases hjU : j = stepConstraintKindIdx kind
    · have hiNe : i ≠ stepConstraintKindIdx kind := by omega
      simp only [hjU, hiNe, ↓reduceIte]
      exact g_mul_zero _
    · simp only [hjU, ↓reduceIte]
      exact g_zero_mul _
  · rw [oneHot_getD_eq kind hMem _ hUidLt]
    simp only [↓reduceIte]
    exact g_sub_self _

private theorem hemStepSelectorInputs_iff (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (sels : List Goldilocks) (permRes boundaryRes : List Goldilocks)
    (hMem : kind ∈ allStepConstraintKinds) (hValid : kind.validSlot = true)
    (hLen : sels.length = allStepConstraintKinds.length) :
    allZeroGoldilocks
        (permRes ++
         boundaryRes ++
         hemStepSelectorBoolResiduals sels ++
         hemStepSelectorOrthResiduals sels ++
         [Goldilocks.one -ₚ sels.getD (stepConstraintKindIdx kind) Goldilocks.zero] ++
         hemStepMuxedInputResiduals c0 x sels) = true ↔
      allZeroGoldilocks
        (permRes ++
         boundaryRes ++
         stepOpConstraints kind c0 x) = true ∧
      sels = oneHotStepSelectors kind := by
  have hSingle : ∀ r : Goldilocks, allZeroGoldilocks [r] = (r == Goldilocks.zero) := by
    intro r; simp [allZeroGoldilocks_eq]
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, hSingle, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨hGA, hBnd⟩, _⟩, hOrth⟩, hPin⟩, hMux⟩
    have hEq := hemStepSelector_oneHot_collapse kind sels hMem hLen hOrth hPin
    rw [hEq] at hMux
    exact ⟨⟨⟨hGA, hBnd⟩, (hemStep_oneHot_mux kind c0 x hMem hValid).mp hMux⟩, hEq⟩
  · rintro ⟨⟨⟨hGA, hBnd⟩, hOp⟩, hEq⟩
    rw [hEq]
    obtain ⟨hBool, hOrth, hPin⟩ := hemStep_oneHot_selectors kind hMem
    exact ⟨⟨⟨⟨⟨hGA, hBnd⟩, hBool⟩, hOrth⟩, hPin⟩,
      (hemStep_oneHot_mux kind c0 x hMem hValid).mpr hOp⟩


private theorem hemStepSelectorRowActive_iff (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (rowsPerSigner t : Nat) (sr : HemStepOpSelectorRow)
    (hMem : kind ∈ allStepConstraintKinds) (hValid : kind.validSlot = true)
    (hLen : sr.sels.length = allStepConstraintKinds.length) :
    allZeroGoldilocks
        ((stepOpPermTrace sr.row).2 ++
         stepOpBoundaryResiduals rowsPerSigner t sr.row ++
         hemStepSelectorBoolResiduals sr.sels ++
         hemStepSelectorOrthResiduals sr.sels ++
         [Goldilocks.one -ₚ sr.sels.getD (stepConstraintKindIdx kind) Goldilocks.zero] ++
         hemStepMuxedOpResiduals (some pub) c0 sr.row sr.sels) = true ↔
      allZeroGoldilocks
        ((stepOpPermTrace sr.row).2 ++
         stepOpBoundaryResiduals rowsPerSigner t sr.row ++
         stepOpConstraints kind c0 (stepOpRowInputs pub sr.row)) = true ∧
      sr.sels = oneHotStepSelectors kind :=
  hemStepSelectorInputs_iff kind c0 (stepOpRowInputs pub sr.row) sr.sels
    (stepOpPermTrace sr.row).2 (stepOpBoundaryResiduals rowsPerSigner t sr.row)
    hMem hValid hLen

private theorem hemStepSelectorRowResiduals_iff (profile : AggSigProfile) (slot : StepOpSlot)
    (t : Nat) (sr : HemStepOpSelectorRow)
    (hLen : sr.sels.length = allStepConstraintKinds.length) :
    allZeroGoldilocks (hemStepSelectorRowResiduals profile slot t sr) = true ↔
      allZeroGoldilocks (stepOp256RowResiduals profile slot t sr.row) = true ∧
      sr.sels = (match slot with
        | none => List.replicate allStepConstraintKinds.length Goldilocks.zero
        | some _ =>
          oneHotStepSelectors (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1) := by
  simp only [hemStepSelectorRowResiduals]
  cases slot with
  | none =>
    simp only [stepOp256RowResiduals.public_eqs]
    unfold hemStepSchedulePinResiduals hemStepMuxedOpResiduals
    simp only [List.append_nil, allZeroGoldilocks_append, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨⟨⟨hGA, hBnd⟩, _⟩, _⟩, hPin⟩
      have hZeroAll := (allZero_map_iff allStepConstraintKinds.length
        (fun k => sr.sels.getD k Goldilocks.zero)).mp hPin
      refine ⟨⟨hGA, hBnd⟩, ?_⟩
      apply List.ext_getElem
      · rw [hLen, List.length_replicate]
      · intro k hk1 _
        have hGet : sr.sels[k]'hk1 = sr.sels.getD k Goldilocks.zero := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1, Option.getD_some]
        rw [hGet, List.getElem_replicate]
        exact hZeroAll k (hLen ▸ hk1)
    · rintro ⟨⟨hGA, hBnd⟩, hSelsEq⟩
      refine ⟨⟨⟨⟨hGA, hBnd⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [hSelsEq]; unfold hemStepSelectorBoolResiduals
        rw [allZero_map_iff]; intro k _
        rw [getD_rep_zero]; exact (stepBoolCheck_eq_zero_iff _).mpr (.inl rfl)
      · rw [hSelsEq, allZero_orth_iff]; intro i j _ _
        rw [getD_rep_zero, g_zero_mul]
      · rw [hSelsEq, allZero_map_iff]; intro k _; exact getD_rep_zero _ _
  | some pub =>
    simp only [stepOp256RowResiduals.public_eqs]
    obtain ⟨hMem, hValid⟩ := buildSignerProgram_kind_mem_and_valid profile t
    unfold hemStepSchedulePinResiduals
    exact hemStepSelectorRowActive_iff
      (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1
      (Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).2)
      pub (stepOpRowsPerSigner profile) t sr hMem hValid hLen

private theorem hemStepSelectorIntraFrom_iff (profile : AggSigProfile) (slots : List StepOpSlot) :
    ∀ (srows : List HemStepOpSelectorRow) (g : Nat),
      (∀ sr ∈ srows, sr.sels.length = allStepConstraintKinds.length) →
      (allZeroGoldilocks (hemStepSelectorIntraFrom profile slots g srows) = true ↔
        allZeroGoldilocks (stepOp256IntraResidualsFrom profile slots g (srows.map HemStepOpSelectorRow.row)) = true ∧
        srows = attachHonestStepSelectorsFrom profile slots g (srows.map HemStepOpSelectorRow.row))
  | [], _, _ => by simp [hemStepSelectorIntraFrom, stepOp256IntraResidualsFrom.public_eqs, attachHonestStepSelectorsFrom]
  | sr :: rest, g, hLens => by
    simp only [List.map_cons, hemStepSelectorIntraFrom, stepOp256IntraResidualsFrom.public_eqs,
      attachHonestStepSelectorsFrom]
    rw [allZeroGoldilocks_append, allZeroGoldilocks_append, Bool.and_eq_true, Bool.and_eq_true,
        hemStepSelectorRowResiduals_iff profile _ _ sr (hLens sr (List.mem_cons_self ..)),
        hemStepSelectorIntraFrom_iff profile slots rest (g + 1)
          (fun x hx => hLens x (List.mem_cons_of_mem _ hx))]
    constructor
    · rintro ⟨⟨hRowOk, hSelEq⟩, hRestOk, hRestEq⟩
      refine ⟨⟨hRowOk, hRestOk⟩, ?_⟩
      rw [← hRestEq]
      cases sr; dsimp only at hSelEq ⊢; subst hSelEq; rfl
    · rintro ⟨⟨hRowOk, hRestOk⟩, hConsEq⟩
      injection hConsEq with hHeadEq hTailEq
      have hSelEq : sr.sels = _ := (congrArg HemStepOpSelectorRow.sels hHeadEq)
      exact ⟨⟨hRowOk, hSelEq⟩, hRestOk, hTailEq⟩

private theorem attachHonestStepSelectorsFrom_map_row (profile : AggSigProfile) (slots : List StepOpSlot) :
    ∀ (rows : List StepOpRow) (g : Nat),
      (attachHonestStepSelectorsFrom profile slots g rows).map HemStepOpSelectorRow.row = rows
  | [], _ => rfl
  | r :: rs, g => congrArg (r :: ·) (attachHonestStepSelectorsFrom_map_row profile slots rs (g + 1))

private theorem attachHonestStepSelectorsFrom_sels_len (profile : AggSigProfile) (slots : List StepOpSlot) :
    ∀ (rows : List StepOpRow) (g : Nat) (sr : HemStepOpSelectorRow),
      sr ∈ attachHonestStepSelectorsFrom profile slots g rows →
      sr.sels.length = allStepConstraintKinds.length
  | [], _, _, h => False.elim (List.not_mem_nil h)
  | r :: rs, g, sr, h => by
    rcases List.mem_cons.mp h with rfl | hTail
    · dsimp only
      cases slots.getD (g / stepOpRowsPerSigner profile) none with
      | none => exact List.length_replicate
      | some _ => unfold oneHotStepSelectors; exact List.length_map ..
    · exact attachHonestStepSelectorsFrom_sels_len profile slots rs (g + 1) sr hTail

/-- **Selector-Muxed 256-Column Equivalence (`hemStepTraceValid_iff_stepOp256TableOk`)**:
    1. Attaching canonical scheduled selectors to any `rows` satisfies `hemStepTraceValid` iff
       `stepOp256TableOk profile slots rows = true`.
    2. Conversely, ANY selector-explicit trace `srows` satisfying `hemStepTraceValid` has
       `srows = attachHonestStepSelectors profile slots (srows.map (·.row))` and
       `stepOp256TableOk profile slots (srows.map (·.row)) = true`. -/
theorem hemStepTraceValid_iff_stepOp256TableOk (profile : AggSigProfile) (slots : List StepOpSlot)
    (srows : List HemStepOpSelectorRow) :
    hemStepTraceValid profile slots srows = true ↔
      stepOp256TableOk profile slots (srows.map HemStepOpSelectorRow.row) = true ∧
      srows = attachHonestStepSelectors profile slots (srows.map HemStepOpSelectorRow.row) := by
  simp only [hemStepTraceValid, stepOp256TableOk.public_eqs, attachHonestStepSelectors]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_map, List.all_map, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨hPos, hLen⟩, hShapedAndSels⟩, hIntra⟩, hShift⟩
    have hShaped : ∀ x ∈ srows, x.row.wellShaped = true := fun x hx => (hShapedAndSels x hx).1
    have hSelsLen : ∀ x ∈ srows, x.sels.length = allStepConstraintKinds.length :=
      fun x hx => (hShapedAndSels x hx).2
    obtain ⟨hIntraRow, hSrowsEq⟩ := (hemStepSelectorIntraFrom_iff profile slots srows 0 hSelsLen).mp hIntra
    exact ⟨⟨⟨⟨⟨hPos, hLen⟩, hShaped⟩, hIntraRow⟩, hShift⟩, hSrowsEq⟩
  · rintro ⟨⟨⟨⟨⟨hPos, hLen⟩, hShaped⟩, hIntraRow⟩, hShift⟩, hSrowsEq⟩
    have hSelsLen : ∀ x ∈ srows, x.sels.length = allStepConstraintKinds.length := by
      intro x hx
      rw [hSrowsEq] at hx
      exact attachHonestStepSelectorsFrom_sels_len profile slots _ 0 x hx
    have hIntra := (hemStepSelectorIntraFrom_iff profile slots srows 0 hSelsLen).mpr ⟨hIntraRow, hSrowsEq⟩
    exact ⟨⟨⟨⟨hPos, hLen⟩, fun x hx => ⟨hShaped x hx, hSelsLen x hx⟩⟩, hIntra⟩, hShift⟩

theorem hemStepTraceValid_attachHonest_iff (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) :
    hemStepTraceValid profile slots (attachHonestStepSelectors profile slots rows) = true ↔
      stepOp256TableOk profile slots rows = true := by
  rw [hemStepTraceValid_iff_stepOp256TableOk]
  unfold attachHonestStepSelectors
  rw [attachHonestStepSelectorsFrom_map_row]
  simp

end SelectorEquiv

/-- A valid active table row executes the scheduled functional transition and satisfies
    its guards; its permutation output is the actual Poseidon2 permutation. This theorem
    projects facts from the original table, without adding a verifier-validity premise. -/
theorem stepOp256TableOk_active_execution (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) (i : Nat) (row : StepOpRow) (pub : AggValidatorPk × Digest5)
    (hTable : stepOp256TableOk profile slots rows = true)
    (hRow : rows[i]? = some row)
    (hSlot : slots.getD (i / stepOpRowsPerSigner profile) none = some pub) :
    let op := (buildSignerProgram profile).getD (i % stepOpRowsPerSigner profile) StepOp.idle
    let kind := (stepOpKindAndC0 op).1
    let c0 := Goldilocks.ofNat (stepOpKindAndC0 op).2
    (stepOpPermTrace row).1 = poseidon2Perm12 row.stIn ∧
    allZeroGoldilocks (stepOpGuardResiduals kind c0 (stepOpRowInputs pub row)) = true ∧
    ∀ j < 44, row.nextState.getD j Goldilocks.zero =
      stepOpExpectedNext kind c0 (stepOpRowInputs pub row) j := by
  have hr := stepOp256TableOk_row_at profile slots rows i row hTable hRow
  rw [hSlot] at hr
  simp only [stepOp256RowResiduals.public_eqs] at hr
  simp only [allZeroGoldilocks_append, Bool.and_eq_true] at hr
  obtain ⟨_, hValid⟩ := buildSignerProgram_kind_mem_and_valid profile
    (i % stepOpRowsPerSigner profile)
  exact ⟨stepOp256_groupA_exact row hr.1.1,
    (stepOpConstraints_iff_guard_and_next _ _ _ hValid).mp hr.2⟩

/-- Populate the 44 next-state cells by executing an opcode. The remaining 212 cells
    are retained. This is an execution constructor, not a native-signature trace builder. -/
@[expose] def populateStepOpNext (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (row : StepOpRow) : StepOpRow :=
  { row with nextState := (List.range 44).map (stepOpExpectedNext kind c0 (stepOpRowInputs pub row)) }

theorem populateStepOpNext_inputs (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (row : StepOpRow) :
    stepOpRowInputs pub (populateStepOpNext kind c0 pub row) =
      { stepOpRowInputs pub row with next := fun j =>
          ((List.range 44).map (stepOpExpectedNext kind c0 (stepOpRowInputs pub row))).getD j Goldilocks.zero } := by
  simp only [populateStepOpNext, stepOpRowInputs.public_eqs, stepOpPermTrace_nextState]

/-- Every scheduled opcode admits exactly its functional next state once its guards
    hold. This covers all active opcode classes, rather than just padding `Idle`. -/
theorem populateStepOpNext_constraints_iff (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (row : StepOpRow)
    (hValid : kind.validSlot = true) :
    allZeroGoldilocks (stepOpConstraints kind c0
      (stepOpRowInputs pub (populateStepOpNext kind c0 pub row))) = true ↔
    allZeroGoldilocks (stepOpGuardResiduals kind c0 (stepOpRowInputs pub row)) = true := by
  rw [stepOpConstraints_iff_guard_and_next kind c0 _ hValid,
    populateStepOpNext_inputs, stepOpGuardResiduals_congr_next]
  have hNext : ∀ j < 44,
      (stepOpRowInputs pub (populateStepOpNext kind c0 pub row)).next j =
        stepOpExpectedNext kind c0 (stepOpRowInputs pub row) j := by
    intro j hj
    simp [stepOpRowInputs.public_eqs, populateStepOpNext, List.getD_eq_getElem?_getD, hj]
  constructor
  · exact And.left
  · intro hGuard
    refine ⟨hGuard, ?_⟩
    intro j hj
    rw [stepOpExpectedNext_congr_next]
    exact hNext j hj

/-- An accepted row is unchanged by recomputing its next-state block. In particular,
    the AIR cannot accept two different 44-cell next states for the same guarded inputs. -/
theorem populateStepOpNext_eq_of_constraints (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (row : StepOpRow)
    (hValid : kind.validSlot = true) (hLen : row.nextState.length = 44)
    (hOk : allZeroGoldilocks (stepOpConstraints kind c0 (stepOpRowInputs pub row)) = true) :
    populateStepOpNext kind c0 pub row = row := by
  have hNext := ((stepOpConstraints_iff_guard_and_next kind c0 _ hValid).mp hOk).2
  have hEq : (List.range 44).map (stepOpExpectedNext kind c0 (stepOpRowInputs pub row)) =
      row.nextState := by
    apply List.ext_getElem
    · simp [hLen]
    · intro i hi hi'
      have hi44 : i < 44 := by simpa using hi
      have he := hNext i hi44
      simpa [stepOpRowInputs.public_eqs, List.getD_eq_getElem?_getD, hi'] using he.symm
  simp [populateStepOpNext, hEq]

/-- Guard/transition completeness for a scheduled active row, with both boundary gates
    retained. Native-verifier completeness still requires constructing inputs satisfying
    these guards along the complete signer program. -/
theorem stepOp256RowResiduals_active_iff (profile : AggSigProfile)
    (pub : AggValidatorPk × Digest5) (t : Nat) (row : StepOpRow) :
    let op := (buildSignerProgram profile).getD t StepOp.idle
    let kind := (stepOpKindAndC0 op).1
    let c0 := Goldilocks.ofNat (stepOpKindAndC0 op).2
    allZeroGoldilocks (stepOp256RowResiduals profile (some pub) t row) = true ↔
      allZeroGoldilocks (stepOpPermTrace row).2 = true ∧
      (∀ j < 44, t = 0 → row.prevState.getD j Goldilocks.zero = Goldilocks.zero) ∧
      (∀ j < 44, t + 1 = stepOpRowsPerSigner profile →
        row.nextState.getD j Goldilocks.zero = Goldilocks.zero) ∧
      allZeroGoldilocks (stepOpGuardResiduals kind c0 (stepOpRowInputs pub row)) = true ∧
      (∀ j < 44, row.nextState.getD j Goldilocks.zero =
        stepOpExpectedNext kind c0 (stepOpRowInputs pub row) j) := by
  dsimp only
  simp only [stepOp256RowResiduals.public_eqs]
  rw [allZeroGoldilocks_append, allZeroGoldilocks_append, Bool.and_eq_true, Bool.and_eq_true,
    stepOpBoundaryResiduals_iff, stepOpConstraints_iff_guard_and_next _ _ _
      (buildSignerProgram_kind_mem_and_valid profile t).2]
  simp only [and_assoc, stepOpRowInputs.public_eqs]

/-- A corrupted next-state limb is rejected even when the other row cells are arbitrary.
    This pairs with the constructor above: the transition gate enforces its computed output. -/
theorem tooth_stepOp_wrong_next_rejected (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (row : StepOpRow) (j : Nat)
    (hValid : kind.validSlot = true) (hj : j < 44)
    (hWrong : row.nextState.getD j Goldilocks.zero ≠
      stepOpExpectedNext kind c0 (stepOpRowInputs pub row) j) :
    allZeroGoldilocks (stepOpConstraints kind c0 (stepOpRowInputs pub row)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact hWrong (((stepOpConstraints_iff_guard_and_next kind c0 _ hValid).mp h).2 j hj)

/-- Populate all permutation columns without assuming any opcode guards. -/
@[expose] def stepOpHonestPermutationRow (input : Poseidon2State12)
    (prev next aux : List Goldilocks) : StepOpRow :=
  let w := honestPoseidon2PermWitness input
  ⟨input, w.initExtSbox, w.intSbox, w.termExtSbox, prev, next, aux⟩

theorem stepOpHonestPermutationRow_groupA (input : Poseidon2State12)
    (prev next aux : List Goldilocks) :
    allZeroGoldilocks (stepOpPermTrace (stepOpHonestPermutationRow input prev next aux)).2 = true := by
  let w := honestPoseidon2PermWitness input
  have h := (poseidon2PermResiduals_allZero_iff w).mpr (by simp only [w, honestPoseidon2PermWitness.public_eqs])
  have he : poseidon2PermResiduals w =
      (stepOpPermTrace (stepOpHonestPermutationRow input prev next aux)).2 ++
      (state12Sub (stepOpPermTrace (stepOpHonestPermutationRow input prev next aux)).1
        w.output).toList := by
    simp only [poseidon2PermResiduals.public_eqs, stepOpPermTrace.public_eqs,
      stepOpHonestPermutationRow, w, honestPoseidon2PermWitness.public_eqs]
  rw [he, allZeroGoldilocks_append, Bool.and_eq_true] at h
  exact h.1

theorem stepOpHonestPermutationRow_wellShaped (input : Poseidon2State12)
    (prev next aux : List Goldilocks)
    (hp : prev.length = 44) (hn : next.length = 44) (ha : aux.length = 38) :
    (stepOpHonestPermutationRow input prev next aux).wellShaped = true := by
  obtain ⟨h1, h2, h3⟩ := honestPoseidon2PermWitness_lengths input
  simp only [stepOpHonestPermutationRow, StepOpRow.wellShaped.public_eqs, h1, h2, h3, hp, hn, ha,
    beq_self_eq_true, Bool.and_self]

/-- A non-padding active opcode has satisfiable guards and a full honest permutation
    witness. This certificate concerns one row; it does not assert a valid whole signer slot. -/
theorem inhabited_populateStepOpNext :
    ∃ (kind : StepConstraintKind) (c0 : Goldilocks)
      (pub : AggValidatorPk × Digest5) (row : StepOpRow),
      kind.validSlot = true ∧ kind ≠ .idle ∧
      allZeroGoldilocks (stepOpGuardResiduals kind c0 (stepOpRowInputs pub row)) = true ∧
      row.wellShaped = true ∧
      allZeroGoldilocks (stepOpPermTrace row).2 = true := by
  let pub : AggValidatorPk × Digest5 :=
    (⟨.corduroyPoseidon2, ⟨‹1›, ‹2›, ‹3›, ‹4›⟩, ⟨‹5›, ‹6›, ‹7›, ‹8›⟩⟩,
      ⟨‹9›, ‹10›, ‹11›, ‹12›, ‹13›⟩)
  let input : Poseidon2State12 :=
    ⟨pub.1.pkSeed, pub.1.pkRoot, ⟨domainHMsgStateless, pub.2.limb4, Goldilocks.zero, poseidon2IvTag⟩⟩
  let row := stepOpHonestPermutationRow input (List.replicate 44 Goldilocks.zero)
    (List.replicate 44 Goldilocks.zero) (List.replicate 38 Goldilocks.zero)
  have hValid : StepConstraintKind.statelessDeriveBlock0.validSlot = true := by
    simp only [StepConstraintKind.validSlot.public_eqs]
  have hNotIdle : StepConstraintKind.statelessDeriveBlock0 ≠ .idle := by intro h; cases h
  refine ⟨.statelessDeriveBlock0, Goldilocks.zero, pub, row, hValid, hNotIdle, ?_, ?_, ?_⟩
  · change allZeroGoldilocks (stepOpGuardResiduals .statelessDeriveBlock0 Goldilocks.zero
      (stepOpRowInputs pub row)) = true
    simp [row, input, pub, stepOpGuardResiduals, stepOpRowInputs.public_eqs,
      stepOpHonestPermutationRow, allZeroGoldilocks_eq, Poseidon2State12.toList_eq,
      Lane4.toList_eq, g_sub_self]
    intro i hi
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hCases with rfl | rfl | rfl | rfl <;> simp [g_sub_self]
  · exact stepOpHonestPermutationRow_wellShaped input _ _ _
      (List.length_replicate ..) (List.length_replicate ..) (List.length_replicate ..)
  · exact stepOpHonestPermutationRow_groupA input _ _ _

#tooth_pair populateStepOpNext_constraints_iff vs tooth_stepOp_wrong_next_rejected
#verify_inhabited populateStepOpNext_constraints_iff inhabited_populateStepOpNext

/-! ### §3.4. Active-slot execution: per-signer row semantics

`stepOp256TableOk` speaks about one flat list of rows. The lemmas below restrict it to one
active signer slot, re-index its rows by the step `t` of `buildSignerProgram`, and expose every
scheduled row as a guarded functional transition of the 44 carried limbs. -/

/-- Row `t` of signer slot `k` of a table (`stepOpZeroRow` outside the table). -/
def stepOpSlotRow (profile : AggSigProfile) (rows : List StepOpRow) (k t : Nat) : StepOpRow :=
  rows.getD (k * stepOpRowsPerSigner profile + t) stepOpZeroRow
#export_eqns stepOpSlotRow

/-- State limb `j` entering row `t`. -/
@[expose] def stepPrev (R : Nat → StepOpRow) (t j : Nat) : Goldilocks :=
  (R t).prevState.getD j Goldilocks.zero

/-- Auxiliary cell `i` of row `t`. -/
@[expose] def stepAux (R : Nat → StepOpRow) (t i : Nat) : Goldilocks :=
  (R t).aux.getD i Goldilocks.zero

theorem stepAux_fun (R : Nat → StepOpRow) (t : Nat) :
    stepAux R t = fun i => (R t).aux.getD i Goldilocks.zero := rfl

/-- Row `t` executes `op`: its permutation columns hold `poseidon2Perm12` of its `COL_ST_IN`
    block, the guards of `op` vanish, and the state entering row `t + 1` is the functional
    next state of `op`. -/
@[expose] def StepRowSem (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow) (op : StepOp)
    (t : Nat) : Prop :=
  (stepOpPermTrace (R t)).1 = poseidon2Perm12 (R t).stIn ∧
  allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
    (Goldilocks.ofNat (stepOpKindAndC0 op).2) (stepOpRowInputs pub (R t))) = true ∧
  ∀ j < 44, stepPrev R (t + 1) j =
    stepOpExpectedNext (stepOpKindAndC0 op).1 (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs pub (R t)) j

private theorem stepOpRowsPerSigner_pos (profile : AggSigProfile) :
    0 < stepOpRowsPerSigner profile := by
  cases profile <;> simp only [stepOpRowsPerSigner.public_eqs] <;> decide

private theorem stepOp256TableOk_slot_row_core (profile : AggSigProfile)
    (slots : List StepOpSlot) (rows : List StepOpRow) (k : Nat) (pub : AggValidatorPk × Digest5)
    (hTable : stepOp256TableOk profile slots rows = true)
    (hSlot : slots[k]? = some (some pub)) (t : Nat)
    (ht : t < stepOpRowsPerSigner profile) :
    rows[k * stepOpRowsPerSigner profile + t]? = some (stepOpSlotRow profile rows k t) ∧
    allZeroGoldilocks (stepOp256RowResiduals profile (some pub) t
      (stepOpSlotRow profile rows k t)) = true := by
  obtain ⟨_, hLen, _, hIntra, _⟩ := (stepOp256TableOk_iff_rows profile slots rows).mp hTable
  have hRpos := stepOpRowsPerSigner_pos profile
  have hk : k < slots.length := (List.getElem?_eq_some_iff.mp hSlot).1
  have h1 : (k + 1) * stepOpRowsPerSigner profile ≤ slots.length * stepOpRowsPerSigner profile :=
    Nat.mul_le_mul_right _ hk
  rw [Nat.succ_mul] at h1
  have hi0 : k * stepOpRowsPerSigner profile + t < rows.length := by omega
  have hRow0 : rows[k * stepOpRowsPerSigner profile + t]? =
      some (stepOpSlotRow profile rows k t) := by
    unfold stepOpSlotRow
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi0]
    rfl
  have hDiv : (k * stepOpRowsPerSigner profile + t) / stepOpRowsPerSigner profile = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hRpos, Nat.div_eq_of_lt ht, Nat.zero_add]
  have hMod : (k * stepOpRowsPerSigner profile + t) % stepOpRowsPerSigner profile = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  have hSlotD : slots.getD k none = some pub := by
    rw [List.getD_eq_getElem?_getD, hSlot]
    rfl
  have hRes := hIntra _ _ hRow0
  rw [hDiv, hMod, hSlotD] at hRes
  exact ⟨hRow0, hRes⟩

/-- Every non-final row of an active slot of a valid table executes its scheduled opcode. -/
theorem stepOp256TableOk_slot_rowSem (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) (k : Nat) (pub : AggValidatorPk × Digest5)
    (hTable : stepOp256TableOk profile slots rows = true)
    (hSlot : slots[k]? = some (some pub)) (t : Nat)
    (ht : t + 1 < stepOpRowsPerSigner profile) :
    StepRowSem pub (stepOpSlotRow profile rows k)
      ((buildSignerProgram profile).getD t StepOp.idle) t := by
  obtain ⟨hRow0, hRes⟩ := stepOp256TableOk_slot_row_core profile slots rows k pub hTable hSlot t
    (by omega)
  obtain ⟨hRow1, _⟩ := stepOp256TableOk_slot_row_core profile slots rows k pub hTable hSlot
    (t + 1) ht
  obtain ⟨_, _, _, _, hShift⟩ := (stepOp256TableOk_iff_rows profile slots rows).mp hTable
  have hA := stepOp256RowResiduals_active_iff profile pub t (stepOpSlotRow profile rows k t)
  dsimp only at hA
  obtain ⟨hGA, _, _, hGuard, hNext⟩ := hA.mp hRes
  refine ⟨stepOp256_groupA_exact _ hGA, hGuard, fun j hj => ?_⟩
  unfold stepPrev
  rw [← hShift _ _ _ hRow0 hRow1 j hj]
  exact hNext j hj

/-- The first row of an active slot of a valid table starts from the zero state. -/
theorem stepOp256TableOk_slot_init (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) (k : Nat) (pub : AggValidatorPk × Digest5)
    (hTable : stepOp256TableOk profile slots rows = true)
    (hSlot : slots[k]? = some (some pub)) :
    ∀ j < 44, stepPrev (stepOpSlotRow profile rows k) 0 j = Goldilocks.zero := by
  obtain ⟨_, hRes⟩ := stepOp256TableOk_slot_row_core profile slots rows k pub hTable hSlot 0
    (stepOpRowsPerSigner_pos profile)
  have hA := stepOp256RowResiduals_active_iff profile pub 0 (stepOpSlotRow profile rows k 0)
  dsimp only at hA
  obtain ⟨_, hInit, _⟩ := hA.mp hRes
  exact fun j hj => hInit j hj rfl

/-- The rows from `t0` on execute the opcodes `ops` in order. -/
@[expose] def StepRunAt (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow) (ops : List StepOp)
    (t0 : Nat) : Prop :=
  ∀ (i : Nat) (hi : i < ops.length), StepRowSem pub R ops[i] (t0 + i)

theorem StepRunAt.get {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {ops : List StepOp} {t0 : Nat} (h : StepRunAt pub R ops t0) (i : Nat) (op : StepOp)
    (hop : ops[i]? = some op) : StepRowSem pub R op (t0 + i) := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hop
  have h' := h i hi
  rw [he] at h'
  exact h'

theorem StepRunAt.head {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {op : StepOp} {ops : List StepOp} {t0 : Nat} (h : StepRunAt pub R (op :: ops) t0) :
    StepRowSem pub R op t0 :=
  h 0 (Nat.zero_lt_succ _)

theorem StepRunAt.tail {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {op : StepOp} {ops : List StepOp} {t0 : Nat} (h : StepRunAt pub R (op :: ops) t0) :
    StepRunAt pub R ops (t0 + 1) := by
  intro i hi
  have h' := h (i + 1) (Nat.succ_lt_succ hi)
  simp only [List.getElem_cons_succ] at h'
  have e : t0 + (i + 1) = t0 + 1 + i := by omega
  rw [e] at h'
  exact h'

theorem StepRunAt.append_left {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {a b : List StepOp} {t0 : Nat} (h : StepRunAt pub R (a ++ b) t0) :
    StepRunAt pub R a t0 := by
  intro i hi
  have h' := h i (by rw [List.length_append]; omega)
  rw [List.getElem_append_left hi] at h'
  exact h'

theorem StepRunAt.append_right {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {a b : List StepOp} {t0 : Nat} (h : StepRunAt pub R (a ++ b) t0) :
    StepRunAt pub R b (t0 + a.length) := by
  intro i hi
  have h' := h (a.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (by omega)] at h'
  simp only [Nat.add_sub_cancel_left] at h'
  rw [← Nat.add_assoc] at h'
  exact h'

theorem flatMap_range_uniform_length (f : Nat → List StepOp) (L : Nat)
    (hL : ∀ i, (f i).length = L) :
    ∀ n : Nat, ((List.range n).flatMap f).length = n * L
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append,
      flatMap_range_uniform_length f L hL n, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, hL n, Nat.succ_mul]

theorem StepRunAt.flatMap_range {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {f : Nat → List StepOp} {L : Nat} (hL : ∀ i, (f i).length = L) :
    ∀ (n : Nat) {t0 : Nat}, StepRunAt pub R ((List.range n).flatMap f) t0 →
      ∀ i < n, StepRunAt pub R (f i) (t0 + i * L)
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, t0, h, i, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at h
    by_cases hin : i < n
    · exact StepRunAt.flatMap_range hL n h.append_left i hin
    · have hEq : i = n := by omega
      subst hEq
      have h' := h.append_right
      rw [flatMap_range_uniform_length f L hL i] at h'
      exact h'

theorem StepRunAt.map_range {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {g : Nat → StepOp} {n t0 : Nat} (h : StepRunAt pub R ((List.range n).map g) t0) :
    ∀ i < n, StepRowSem pub R (g i) (t0 + i) := by
  intro i hi
  have h' := h i (by rw [List.length_map, List.length_range]; exact hi)
  rw [List.getElem_map, List.getElem_range] at h'
  exact h'

/-- The rows of an active slot of a valid table execute the signer program body. -/
theorem stepOp256TableOk_slot_run (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) (k : Nat) (pub : AggValidatorPk × Digest5)
    (hTable : stepOp256TableOk profile slots rows = true)
    (hSlot : slots[k]? = some (some pub)) :
    StepRunAt pub (stepOpSlotRow profile rows k) (signerProgramBody profile) 0 := by
  intro i hi
  have hLt : (signerProgramBody profile).length + 1 < stepOpRowsPerSigner profile := by
    cases profile with
    | xmssPoseidon2 => rw [buildSignerProgram_length.1]; simp only [stepOpRowsPerSigner.public_eqs]; decide
    | corduroyPoseidon2 => rw [buildSignerProgram_length.2.1]; simp only [stepOpRowsPerSigner.public_eqs]; decide
  have h := stepOp256TableOk_slot_rowSem profile slots rows k pub hTable hSlot i (by omega)
  have hGet : (buildSignerProgram profile).getD i StepOp.idle = (signerProgramBody profile)[i] := by
    simp only [buildSignerProgram.public_eqs]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
    rfl
  rw [hGet] at h
  rw [Nat.zero_add]
  exact h


end HemStepOp256Machine
end Qsag
end

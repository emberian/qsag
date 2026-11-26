module
/-
# `HmsgDecompLimb` Rows, One Full Layer, and `XmssPoseidon2` Signature Extraction

The `HmsgDecompLimb` rows produce the packed remaining-step counts and the target sum; digits,
WOTS+C and Merkle rows of one full layer give `verifyWotsLayer`; and the active `XmssPoseidon2`
slot: an accepted table yields a native signature (`stepOp256TableOk_xmss_extract`).
-/

public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.StepOp256WotsChainRows

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
set_option autoImplicit false
set_option maxErrors 1000
set_option Elab.async false
set_option exponentiation.threshold 2048
attribute [local irreducible] poseidon2Perm12

section HemStepOp256Machine
local infixl:65 " +ₚ " => Goldilocks.add
local infixl:65 " -ₚ " => Goldilocks.sub
local infixl:70 " *ₚ " => Goldilocks.mul
local notation "‹" n "›" => Goldilocks.ofNat n
/-- Normalize only the public guard equations and row projections used by residual indexing. -/
local macro "step_guard_nf " h:ident : tactic =>
  `(tactic| try simp [stepOpKindAndC0.public_eqs, stepOpGuardResiduals,
      stepSpongeAbsorbInput.public_eqs, stepSqueezeInput.public_eqs,
      stepWotsStepInput.public_eqs, stepMerkleBlockBInput.public_eqs,
      stepMerkleBlockAGuards, stepLimb63Decomp_eq,
      stepOpRowInputsPerm, stepOpRowInputs.public_eqs,
      Poseidon2State12.toList_eq, Lane4.toList_eq, lane4Add_eq,
      List.range_succ, List.range_zero] at $h:term)
local macro "gz% " h:ident k:num : term =>
  `(by
    have hNorm := $h
    step_guard_nf hNorm
    apply g_sub_eq_zero_iff.mp
    simpa [lane4Add_eq, stepForsIdxF, StepRem.get, stepAuxLane, stepAux_fun, stepAux, stepPermAt, stepOpRowInputsPerm, stepOpRowInputs.public_eqs,
      Poseidon2State12.toList_eq, Lane4.toList_eq, stepRegsAt, stepRegs, stepPrev, stCurRoot.public_eqs, stKpIdx.public_eqs, stTreeLo.public_eqs, stTreeHi.public_eqs, stRemPack.public_eqs, stMainSponge.public_eqs, stSubSponge.public_eqs, stWork.public_eqs, stCursorIdx.public_eqs, stAccOrU1.public_eqs, stWotsU2.public_eqs] using
      (allZero_getElem hNorm $k (Nat.le_of_ble_eq_true rfl)))
local macro "gzz% " h:ident k:num : term =>
  `(by
    have hNorm := $h
    step_guard_nf hNorm
    simpa [lane4Add_eq, stepForsIdxF, StepRem.get, stepAuxLane, stepAux_fun, stepAux, stepPermAt, stepOpRowInputsPerm, stepOpRowInputs.public_eqs,
      Poseidon2State12.toList_eq, Lane4.toList_eq, stepRegsAt, stepRegs, stepPrev, stCurRoot.public_eqs, stKpIdx.public_eqs, stTreeLo.public_eqs, stTreeHi.public_eqs, stRemPack.public_eqs, stMainSponge.public_eqs, stSubSponge.public_eqs, stWork.public_eqs, stCursorIdx.public_eqs, stAccOrU1.public_eqs, stWotsU2.public_eqs] using
      (allZero_getElem hNorm $k (Nat.le_of_ble_eq_true rfl)))
/-- Compare register limbs separately so kernel conversion does not have to unfold a whole
    symbolic Poseidon permutation to establish a structure equality. -/
local macro "regs% " h:ident : term =>
  `(by
    refine ($h).regs.trans ?_
    simp only [stepRegs, StepRegs.mk.injEq]
    repeat' apply And.intro
    all_goals try apply Poseidon2State12.ext
    all_goals try apply Lane4.ext
    all_goals as_aux_lemma =>
      simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow,
      Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceBEq,
      reduceIte, decide_true, decide_false, Bool.not_false, Bool.not_true,
      Bool.true_eq_false, Bool.false_eq_true, Bool.and_true, Bool.true_and,
      Bool.and_false, Bool.false_and, true_or, or_true, false_or, or_false,
      ne_eq, not_false_eq_true, not_true_eq_false,
      stepOpKindAndC0.public_eqs, stepOpExpectedNext, stepForsIdxF, stepMerkleBlockAExpectedNext, StepRem.get, StepRem.set.public_eqs,
      stepRegsAt, stepRegs, stepOpRowInputsPerm, stepOpRowInputs.public_eqs,
      Poseidon2State12.toList_eq, Lane4.toList_eq, lane4Add_eq, lane4Scale_eq,
      poseidon2WeightedFeedForward_eq, stepRemZero, stepInBlock.public_eqs, stepPrev, stepAux_fun, stepAux,
      stepPermAt, stepFfAt.public_eqs, stepAuxLane, lane4Mux.public_eqs, state12Zero_eq, lane4Zero_eq,
      stepStatelessDecompExpected_frame, stepStatelessDecompExpected_pack_frame,
      stepStatelessDecompExpected_five,
      stepStatelessDecompExpected_six, stepHmsgDecompExpected_frame,
      stepHi28.public_eqs,
      List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, Option.getD_none, Option.getD_some, stCurRoot.public_eqs, stKpIdx.public_eqs, stTreeLo.public_eqs, stTreeHi.public_eqs, stRemPack.public_eqs, stMainSponge.public_eqs, stSubSponge.public_eqs, stWork.public_eqs, stCursorIdx.public_eqs, stAccOrU1.public_eqs, stWotsU2.public_eqs])

/-! ### §3.11. `HmsgDecompLimb` rows: the packed remaining-step counts and the target sum -/

/-- Limb `l` of a `Digest5` (the last limb for `l ≥ 4`). -/
@[expose] def digest5Limb (d : Digest5) : Nat → Goldilocks
  | 0 => d.limb0
  | 1 => d.limb1
  | 2 => d.limb2
  | 3 => d.limb3
  | _ => d.limb4

/-- Base-4 digit of chain `c`: digit `c % 31` of limb `c / 31`. -/
@[expose] def stepDigit (d : Digest5) (c : Nat) : Nat :=
  ((digest5Limb d (c / 31)).val / 4 ^ (c % 31)) % 4

/-- The `H_msg` digest held in the first five limbs of `ST_MAIN_SPONGE`. -/
@[expose] def stepHmsgOf (m : Poseidon2State12) : Digest5 :=
  ⟨m.b0.x0, m.b0.x1, m.b0.x2, m.b0.x3, m.b1.x0⟩

/-- Digits `dig c` of the items `cs` owned by slot `s`, packed in base `B` from the first item
    `start s` of the slot, accumulated onto `a`. -/
@[expose] def stepPackFoldG (B : Nat) (slotOf start : Nat → Nat) (dig : Nat → Nat) (s : Nat)
    (cs : List Nat) (a : Nat) : Nat :=
  cs.foldl (fun acc c => if slotOf c = s then acc + dig c * B ^ (c - start s) else acc) a

/-- Remaining-step counts `3 - dg c` of the chains `cs` owned by slot `s`, packed two bits per
    chain from the first chain of the slot, accumulated onto `a`. -/
def stepPackFold (dg : Nat → Nat) (s : Nat) (cs : List Nat) (a : Nat) : Nat :=
  stepPackFoldG 4 wotsPackSlot wotsPackSlotStart (fun c => 3 - dg c) s cs a

private theorem g_ofNat_sub_of_le {a b : Nat} (h : b ≤ a) : (‹a› : Goldilocks) -ₚ ‹b› = ‹a - b› := by
  have h1 : (‹b› : Goldilocks) +ₚ (‹a› -ₚ ‹b›) = ‹a› := LawfulCommRing.add_sub_cancel_left _ _
  have h2 : (‹b› : Goldilocks) +ₚ ‹a - b› = ‹a› := by
    rw [← g_ofNat_add]
    exact congrArg Goldilocks.ofNat (by omega)
  exact LawfulCommRing.add_left_cancel (h1.trans h2.symm)

theorem range'_split : ∀ (m s n : Nat),
    List.range' s (m + n) = List.range' s m ++ List.range' (s + m) n
  | 0, s, n => by simp
  | m + 1, s, n => by
    have e : m + 1 + n = (m + n) + 1 := by omega
    have e2 : s + (m + 1) = s + 1 + m := by omega
    rw [e, e2]
    show s :: List.range' (s + 1) (m + n) = s :: (List.range' (s + 1) m ++ _)
    rw [range'_split m (s + 1) n]

theorem mem_range'_bounds : ∀ (n s c : Nat), c ∈ List.range' s n → s ≤ c ∧ c < s + n
  | 0, _, _, h => absurd h List.not_mem_nil
  | n + 1, s, c, h => by
    have e : List.range' s (n + 1) = s :: List.range' (s + 1) n := rfl
    rw [e, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨Nat.le_refl _, by omega⟩
    · have h' := mem_range'_bounds n (s + 1) c h
      exact ⟨by omega, by omega⟩

theorem range'_eq_map (s n : Nat) :
    List.range' s n = (List.range n).map (fun i => s + i) :=
  List.range'_eq_map_range

private theorem stepPackFold_field (x : StepOpRowInputs) (dg : Nat → Nat) (l s : Nat) :
    ∀ (is : List Nat) (A : Nat),
      (∀ i ∈ is, x.aux i = ‹dg (31 * l + i)› ∧ dg (31 * l + i) ≤ 3) →
      is.foldl (fun acc i =>
          if stRemPack + wotsPackSlot (31 * l + i) = stRemPack + s then
            acc +ₚ ((‹3› -ₚ x.aux i) *ₚ
              ‹2 ^ (2 * (31 * l + i - wotsPackSlotStart (wotsPackSlot (31 * l + i))))›)
          else acc) ‹A› =
        ‹stepPackFold dg s (is.map (fun i => 31 * l + i)) A›
  | [], _, _ => rfl
  | i :: rest, A, h => by
    obtain ⟨hAux, hLe⟩ := h i (List.mem_cons_self ..)
    have ih := fun A' => stepPackFold_field x dg l s rest A'
      (fun j hj => h j (List.mem_cons_of_mem _ hj))
    rw [List.foldl_cons, List.map_cons]
    unfold stepPackFold stepPackFoldG
    rw [List.foldl_cons]
    by_cases hc : wotsPackSlot (31 * l + i) = s
    · simp only [hc, ↓reduceIte]
      have hStep : (‹A› : Goldilocks) +ₚ ((‹3› -ₚ x.aux i) *ₚ
          ‹2 ^ (2 * (31 * l + i - wotsPackSlotStart s))›) =
          ‹A + (3 - dg (31 * l + i)) * 4 ^ (31 * l + i - wotsPackSlotStart s)› := by
        rw [hAux, g_ofNat_sub_of_le hLe, ← g_ofNat_mul, ← g_ofNat_add, Nat.pow_mul]
      rw [hStep]
      exact ih _
    · have hcond : ¬ (stRemPack + wotsPackSlot (31 * l + i) = stRemPack + s) :=
        fun h' => hc (Nat.add_left_cancel h')
      simp only [hcond, hc, ↓reduceIte]
      exact ih _

theorem stepPlainSum_field (x : StepOpRowInputs) (dg : Nat → Nat) (l : Nat) :
    ∀ (is : List Nat) (A : Nat),
      (∀ i ∈ is, x.aux i = ‹dg (31 * l + i)›) →
      is.foldl (fun acc i => acc +ₚ x.aux i) ‹A› =
        ‹A + listNatSum (is.map (fun i => dg (31 * l + i)))›
  | [], _, _ => by simp only [List.foldl_nil, List.map_nil, listNatSum.public_eqs, Nat.add_zero]
  | i :: rest, A, h => by
    rw [List.foldl_cons, h i (List.mem_cons_self ..), ← g_ofNat_add,
      stepPlainSum_field x dg l rest _ (fun j hj => h j (List.mem_cons_of_mem _ hj)),
      List.map_cons]
    exact congrArg Goldilocks.ofNat (by simp only [listNatSum.public_eqs]; omega)

theorem listNatSum_append : ∀ (a b : List Nat),
    listNatSum (a ++ b) = listNatSum a + listNatSum b
  | [], _ => by simp [listNatSum.public_eqs]
  | x :: a, b => by
    rw [List.cons_append]
    simp only [listNatSum.public_eqs]
    rw [listNatSum_append a b]
    omega

private theorem listNatSum_le (k : Nat) : ∀ (l : List Nat), (∀ x ∈ l, x ≤ k) →
    listNatSum l ≤ k * l.length
  | [], _ => by simp [listNatSum.public_eqs]
  | x :: l, h => by
    have hx := h x (List.mem_cons_self ..)
    have ih := listNatSum_le k l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [listNatSum.public_eqs, List.length_cons, Nat.mul_succ]
    omega

theorem stepDigit_le (d : Digest5) (c : Nat) : stepDigit d c ≤ 3 := by
  unfold stepDigit
  have := Nat.mod_lt ((digest5Limb d (c / 31)).val / 4 ^ (c % 31)) (by decide : 0 < 4)
  omega

/-- Number of digits read from limb `l`. -/
@[expose] def stepLimbDigits (l : Nat) : Nat := if l < 4 then 31 else 4

/-- **`HmsgDecompLimb l` row.** The limb is `< 2^63`; its digits' remaining-step counts are
    added to the `ST_REM_PACK` limbs and the digits to the accumulator; nothing else changes. -/
theorem stepDecomp_row {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow} {l t : Nat}
    (hl : l < 5) (h : StepRowSem pub R (.hmsgDecompLimb l) t) (A : Nat → Nat) (B : Nat)
    (hRem : ∀ s < 6, (stepRegsAt R t).rem.get s = ‹A s›)
    (hAcc : (stepRegsAt R t).acc = ‹B›) :
    (digest5Limb (stepHmsgOf (stepRegsAt R t).main) l).val < 2 ^ 63 ∧
    (∀ s < 6, (stepRegsAt R (t + 1)).rem.get s =
      ‹stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s
        (List.range' (31 * l) (stepLimbDigits l)) (A s)›) ∧
    (stepRegsAt R (t + 1)).acc =
      ‹B + listNatSum ((List.range' (31 * l) (stepLimbDigits l)).map
        (stepDigit (stepHmsgOf (stepRegsAt R t).main)))› ∧
    (l = 4 → (‹B + listNatSum ((List.range' (31 * l) (stepLimbDigits l)).map
        (stepDigit (stepHmsgOf (stepRegsAt R t).main)))› : Goldilocks) = ‹192›) ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := (stepRegsAt R (t + 1)).rem, acc := (stepRegsAt R (t + 1)).acc } := by
  obtain ⟨hD, h192, hR⟩ := stepSem_hmsgDecompLimb hl h
  obtain ⟨hLt, hAux, _⟩ := (stepLimb63Decomp_allZero_iff _ l).mp hD
  have hLimb : (stepOpRowInputsPerm pub (R t)).prev (stMainSponge + l) =
      digest5Limb (stepHmsgOf (stepRegsAt R t).main) l := by
    rcases l with _ | _ | _ | _ | _ | l
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hl (by omega)
  rw [hLimb] at hLt hAux
  have hn : stepLimbDigits l ≤ 31 := by unfold stepLimbDigits; split <;> omega
  have hDig : ∀ i < stepLimbDigits l,
      (stepOpRowInputsPerm pub (R t)).aux i =
        ‹stepDigit (stepHmsgOf (stepRegsAt R t).main) (31 * l + i)› := by
    intro i hi
    have e1 : (31 * l + i) / 31 = l := by omega
    have e2 : (31 * l + i) % 31 = i := by omega
    unfold stepDigit
    rw [e1, e2]
    exact hAux i (by omega)
  have hRemE : ∀ s < 6, stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l (stRemPack + s) =
      ‹stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s
        (List.range' (31 * l) (stepLimbDigits l)) (A s)› := by
    intro s hs
    have hPrev : (stepOpRowInputsPerm pub (R t)).prev (stRemPack + s) = ‹A s› := by
      rw [← hRem s hs]
      rcases s with _ | _ | _ | _ | _ | _ | s
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd hs (by omega)
    have hne : ¬ (stRemPack + s = stAccOrU1) := by simp only [stRemPack.public_eqs, stAccOrU1.public_eqs]; omega
    simp only [stepHmsgDecompExpected.public_eqs]
    simp only [hne, ↓reduceIte]
    rw [hPrev, range'_eq_map]
    exact stepPackFold_field _ _ l s _ (A s)
      (fun i hi => ⟨hDig i (List.mem_range.mp hi), stepDigit_le _ _⟩)
  have hAccE : stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l stAccOrU1 =
      ‹B + listNatSum ((List.range' (31 * l) (stepLimbDigits l)).map
        (stepDigit (stepHmsgOf (stepRegsAt R t).main)))› := by
    have hPrev : (stepOpRowInputsPerm pub (R t)).prev stAccOrU1 = ‹B› := hAcc
    have hS := stepPlainSum_field (stepOpRowInputsPerm pub (R t))
      (stepDigit (stepHmsgOf (stepRegsAt R t).main)) l (List.range (stepLimbDigits l)) 0
      (fun i hi => hDig i (List.mem_range.mp hi))
    simp only [stepHmsgDecompExpected.public_eqs]
    simp only [↓reduceIte]
    rw [hPrev]
    simp only [stepPlainSum.public_eqs]
    show ‹B› +ₚ (List.range (stepLimbDigits l)).foldl
      (fun acc i => acc +ₚ (stepOpRowInputsPerm pub (R t)).aux i) ‹0› = _
    rw [hS, ← g_ofNat_add, range'_eq_map, List.map_map, Nat.zero_add]
    rfl
  have hRemGet : ∀ s < 6, (stepRegsAt R (t + 1)).rem.get s =
      stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l (stRemPack + s) := by
    intro s hs
    rw [hR]
    rcases s with _ | _ | _ | _ | _ | _ | s
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hs (by omega)
  have hAccGet : (stepRegsAt R (t + 1)).acc =
      stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l stAccOrU1 := by rw [hR]
  refine ⟨hLt, fun s hs => (hRemGet s hs).trans (hRemE s hs), hAccGet.trans hAccE,
    fun h4 => hAccE.symm.trans (h192 h4), ?_⟩
  rw [hR]

theorem stepPackFoldG_append (B : Nat) (slotOf start dig : Nat → Nat) (s : Nat)
    (xs ys : List Nat) (a : Nat) :
    stepPackFoldG B slotOf start dig s (xs ++ ys) a =
      stepPackFoldG B slotOf start dig s ys (stepPackFoldG B slotOf start dig s xs a) := by
  unfold stepPackFoldG
  rw [List.foldl_append]

private theorem stepPackFoldG_skip (B : Nat) (slotOf start dig : Nat → Nat) (s : Nat) :
    ∀ (cs : List Nat) (a : Nat), (∀ c ∈ cs, slotOf c ≠ s) →
      stepPackFoldG B slotOf start dig s cs a = a
  | [], _, _ => rfl
  | c :: cs, a, h => by
    have hc := h c (List.mem_cons_self ..)
    unfold stepPackFoldG
    rw [List.foldl_cons]
    simp only [hc, ↓reduceIte]
    exact stepPackFoldG_skip B slotOf start dig s cs a
      (fun y hy => h y (List.mem_cons_of_mem _ hy))

private theorem stepPackFoldG_run (B : Nat) (slotOf start dig : Nat → Nat) (s : Nat) :
    ∀ (len b acc : Nat), start s ≤ b →
      (∀ c ∈ List.range' b len, slotOf c = s) →
      stepPackFoldG B slotOf start dig s (List.range' b len) acc =
        acc + B ^ (b - start s) * evalBaseDigits B ((List.range' b len).map dig)
  | 0, b, acc, _, _ => by
    show acc = acc + B ^ (b - start s) * 0
    rw [Nat.mul_zero, Nat.add_zero]
  | len + 1, b, acc, hab, h => by
    have e : List.range' b (len + 1) = b :: List.range' (b + 1) len := rfl
    have hb : slotOf b = s := h b (by rw [e]; exact List.mem_cons_self ..)
    have ih := stepPackFoldG_run B slotOf start dig s len (b + 1)
      (acc + dig b * B ^ (b - start s))
      (by omega) (fun c hc => h c (by rw [e]; exact List.mem_cons_of_mem _ hc))
    have hStep : stepPackFoldG B slotOf start dig s (List.range' b (len + 1)) acc =
        stepPackFoldG B slotOf start dig s (List.range' (b + 1) len)
          (acc + dig b * B ^ (b - start s)) := by
      rw [e]
      unfold stepPackFoldG
      rw [List.foldl_cons]
      simp only [hb, ↓reduceIte]
    have hP : B ^ (b + 1 - start s) = B ^ (b - start s) * B := by
      rw [show b + 1 - start s = (b - start s) + 1 by omega, Nat.pow_succ]
    rw [hStep, ih, e, List.map_cons]
    show acc + dig b * B ^ (b - start s) +
        B ^ (b + 1 - start s) * evalBaseDigits B ((List.range' (b + 1) len).map dig) =
      acc + B ^ (b - start s) *
        (dig b + B * evalBaseDigits B ((List.range' (b + 1) len).map dig))
    rw [hP, Nat.mul_add, Nat.mul_comm (dig b), Nat.mul_assoc, Nat.add_assoc]

/-- The packed limb of slot `s` over all `N` items is the base-`B` number of the digits of the
    items `[a, a + len)` the slot owns. -/
theorem stepPackFoldG_slot (B : Nat) (slotOf start dig : Nat → Nat) (N s a len : Nat)
    (hRange : ∀ c < N, slotOf c = s ↔ a ≤ c ∧ c < a + len) (haN : a + len ≤ N)
    (hStart : start s = a) :
    stepPackFoldG B slotOf start dig s (List.range' 0 N) 0 =
      evalBaseDigits B ((List.range' a len).map dig) := by
  have e : List.range' 0 N =
      List.range' 0 a ++ (List.range' a len ++ List.range' (a + len) (N - (a + len))) := by
    have h1 := range'_split a 0 (N - a)
    have h2 := range'_split len a (N - (a + len))
    rw [show a + (N - a) = N by omega, Nat.zero_add] at h1
    rw [show len + (N - (a + len)) = N - a by omega] at h2
    rw [h1, h2]
  have s1 := stepPackFoldG_skip B slotOf start dig s (List.range' 0 a) 0 (fun c hc h' => by
    have hb := mem_range'_bounds _ _ _ hc
    have := (hRange c (by omega)).mp h'
    omega)
  have s2 := stepPackFoldG_run B slotOf start dig s len a 0 (by omega) (fun c hc => by
    have hb := mem_range'_bounds _ _ _ hc
    exact (hRange c (by omega)).mpr hb)
  have s3 := fun acc => stepPackFoldG_skip B slotOf start dig s
    (List.range' (a + len) (N - (a + len))) acc
    (fun c hc h' => by
      have hb := mem_range'_bounds _ _ _ hc
      have := (hRange c (by omega)).mp h'
      omega)
  rw [e, stepPackFoldG_append, stepPackFoldG_append, s1, s2, s3, hStart, Nat.sub_self,
    Nat.pow_zero, Nat.one_mul, Nat.zero_add]

private theorem stepPackFold_append (dg : Nat → Nat) (s : Nat) (xs ys : List Nat) (a : Nat) :
    stepPackFold dg s (xs ++ ys) a = stepPackFold dg s ys (stepPackFold dg s xs a) :=
  stepPackFoldG_append _ _ _ _ _ _ _ _

/-- The packed limb of slot `s` over all 128 chains is the base-4 number of the
    remaining-step counts of the chains `[a, a + len)` the slot owns. -/
theorem stepPackFold_slot (dg : Nat → Nat) (s a len : Nat)
    (hRange : ∀ c < 128, wotsPackSlot c = s ↔ a ≤ c ∧ c < a + len) (haN : a + len ≤ 128)
    (hStart : wotsPackSlotStart s = a) :
    stepPackFold dg s (List.range' 0 128) 0 =
      evalBaseDigits 4 ((List.range' a len).map (fun c => 3 - dg c)) :=
  stepPackFoldG_slot 4 wotsPackSlot wotsPackSlotStart (fun c => 3 - dg c) 128 s a len hRange haN
    hStart

private theorem range'_128_split :
    List.range' 0 128 =
      List.range' 0 31 ++ List.range' 31 31 ++ List.range' 62 31 ++ List.range' 93 31 ++
        List.range' 124 4 := by
  decide

theorem goldilocksPrime_eq : goldilocksPrime = 18446744069414584321 := rfl

/-- **`HmsgDecompLimb` rows.** The five rows check every limb `< 2^63`, leave in each
    `ST_REM_PACK` limb the packed remaining-step counts of its chains, and enforce the target
    sum `192` of the 128 digits. -/
theorem stepDecomp_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow} {t : Nat}
    (hRun : StepRunAt pub R ((List.range 5).map StepOp.hmsgDecompLimb) t)
    (hRem0 : ∀ s < 6, (stepRegsAt R t).rem.get s = Goldilocks.zero)
    (hAcc0 : (stepRegsAt R t).acc = Goldilocks.zero) :
    checkDigest5Limbs63 (stepHmsgOf (stepRegsAt R t).main) = true ∧
    (∀ s < 6, (stepRegsAt R (t + 5)).rem.get s =
      ‹stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 0 128) 0›) ∧
    listNatSum ((List.range' 0 128).map (stepDigit (stepHmsgOf (stepRegsAt R t).main))) = 192 ∧
    (stepRegsAt R (t + 5)).main = (stepRegsAt R t).main ∧
    (stepRegsAt R (t + 5)).curRoot = (stepRegsAt R t).curRoot ∧
    (stepRegsAt R (t + 5)).kp = (stepRegsAt R t).kp ∧
    (stepRegsAt R (t + 5)).treeLo = (stepRegsAt R t).treeLo ∧
    (stepRegsAt R (t + 5)).treeHi = (stepRegsAt R t).treeHi := by
  have hz : (‹0› : Goldilocks) = Goldilocks.zero := Goldilocks.ext rfl
  have h0 : StepRowSem pub R (.hmsgDecompLimb 0) t := hRun.map_range 0 (by decide)
  have h1 : StepRowSem pub R (.hmsgDecompLimb 1) (t + 1) := hRun.map_range 1 (by decide)
  have h2 : StepRowSem pub R (.hmsgDecompLimb 2) (t + 2) := hRun.map_range 2 (by decide)
  have h3 : StepRowSem pub R (.hmsgDecompLimb 3) (t + 3) := hRun.map_range 3 (by decide)
  have h4 : StepRowSem pub R (.hmsgDecompLimb 4) (t + 4) := hRun.map_range 4 (by decide)
  obtain ⟨l0, r0, a0, _, f0⟩ := stepDecomp_row (by decide) h0 (fun _ => 0) 0
    (fun s hs => (hRem0 s hs).trans hz.symm) (hAcc0.trans hz.symm)
  simp only [stepLimbDigits, Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r0 a0
  have m1 : (stepRegsAt R (t + 1)).main = (stepRegsAt R t).main := by rw [f0]
  obtain ⟨l1, r1, a1, _, f1⟩ := stepDecomp_row (by decide) h1 _ _ r0 a0
  have f1' : stepRegsAt R (t + 2) = _ := f1
  rw [m1] at l1 r1 a1
  simp only [stepLimbDigits, Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r1 a1
  have m2 : (stepRegsAt R (t + 2)).main = (stepRegsAt R t).main := by rw [f1']; exact m1
  obtain ⟨l2, r2, a2, _, f2⟩ := stepDecomp_row (by decide) h2 _ _ r1 a1
  have f2' : stepRegsAt R (t + 3) = _ := f2
  rw [m2] at l2 r2 a2
  simp only [stepLimbDigits, Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r2 a2
  have m3 : (stepRegsAt R (t + 3)).main = (stepRegsAt R t).main := by rw [f2']; exact m2
  obtain ⟨l3, r3, a3, _, f3⟩ := stepDecomp_row (by decide) h3 _ _ r2 a2
  have f3' : stepRegsAt R (t + 4) = _ := f3
  rw [m3] at l3 r3 a3
  simp only [stepLimbDigits, Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r3 a3
  have m4 : (stepRegsAt R (t + 4)).main = (stepRegsAt R t).main := by rw [f3']; exact m3
  obtain ⟨l4, r4, _, e192, f4⟩ := stepDecomp_row (by decide) h4 _ _ r3 a3
  have f4' : stepRegsAt R (t + 5) = _ := f4
  have e192' := e192 rfl
  rw [m4] at l4 r4 e192'
  simp only [stepLimbDigits, Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r4 e192'
  have m5 : (stepRegsAt R (t + 5)).main = (stepRegsAt R t).main := by rw [f4']; exact m4
  refine ⟨?_, ?_, ?_, m5, ?_, ?_, ?_, ?_⟩
  · simp only [checkDigest5Limbs63.public_eqs]
    have q0 : (stepHmsgOf (stepRegsAt R t).main).limb0.val < 2 ^ 63 := l0
    have q1 : (stepHmsgOf (stepRegsAt R t).main).limb1.val < 2 ^ 63 := l1
    have q2 : (stepHmsgOf (stepRegsAt R t).main).limb2.val < 2 ^ 63 := l2
    have q3 : (stepHmsgOf (stepRegsAt R t).main).limb3.val < 2 ^ 63 := l3
    have q4 : (stepHmsgOf (stepRegsAt R t).main).limb4.val < 2 ^ 63 := l4
    simp only [q0, q1, q2, q3, q4, decide_true, Bool.and_self]
  · intro s hs
    have h := r4 s hs
    have e : stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 0 128) 0 =
        stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 124 4)
          (stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 93 31)
            (stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 62 31)
              (stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 31 31)
                (stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s
                  (List.range' 0 31) 0)))) := by
      rw [range'_128_split, stepPackFold_append, stepPackFold_append, stepPackFold_append,
        stepPackFold_append]
    rw [e]
    exact h
  · have hv := congrArg Goldilocks.val e192'
    simp only [Goldilocks.ofNat_val] at hv
    have hLe : ∀ (b n : Nat), listNatSum ((List.range' b n).map
        (stepDigit (stepHmsgOf (stepRegsAt R t).main))) ≤ 3 * n := by
      intro b n
      have h := listNatSum_le 3 ((List.range' b n).map
        (stepDigit (stepHmsgOf (stepRegsAt R t).main))) (fun x hx => by
          obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
          exact stepDigit_le _ _)
      rw [List.length_map, List.length_range'] at h
      exact h
    have b0 := hLe 0 31
    have b1 := hLe 31 31
    have b2 := hLe 62 31
    have b3 := hLe 93 31
    have b4 := hLe 124 4
    rw [goldilocksPrime_eq] at hv
    rw [range'_128_split, List.map_append, List.map_append, List.map_append, List.map_append,
      listNatSum_append, listNatSum_append, listNatSum_append, listNatSum_append]
    omega
  · rw [f4', f3', f2', f1', f0]
  · rw [f4', f3', f2', f1', f0]
  · rw [f4', f3', f2', f1', f0]
  · rw [f4', f3', f2', f1', f0]

private theorem extractLimbBase4Digits_map (n v : Nat) :
    extractLimbBase4Digits n v = (List.range n).map (fun i => (v / 4 ^ i) % 4) := by
  apply List.ext_getElem
  · rw [extractLimbBase4Digits_length, List.length_map, List.length_range]
  · intro i h1 h2
    rw [extractLimbBase4Digits_getElem n v i h1, List.getElem_map, List.getElem_range]

private theorem stepDigit_segment (d : Digest5) (l n : Nat) (hn : n ≤ 31) :
    (List.range' (31 * l) n).map (stepDigit d) =
      extractLimbBase4Digits n (digest5Limb d l).val := by
  rw [extractLimbBase4Digits_map, range'_eq_map, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have e1 : (31 * l + i) / 31 = l := by omega
  have e2 : (31 * l + i) % 31 = i := by omega
  show stepDigit d (31 * l + i) = _
  unfold stepDigit
  rw [e1, e2]

/-- The 128 digits `stepDigit` are the digits the native verifier extracts. -/
theorem stepDigits_extract (geom : AggSigGeometry) (d : Digest5)
    (hw : geom.wotsChains = 128) (hChk : checkDigest5Limbs63 d = true) :
    extractWotsDigitsChecked geom d = some ((List.range' 0 128).map (stepDigit d)) := by
  have s0 : (List.range' 0 31).map (stepDigit d) = extractLimbBase4Digits 31 d.limb0.val :=
    stepDigit_segment d 0 31 (by decide)
  have s1 : (List.range' 31 31).map (stepDigit d) = extractLimbBase4Digits 31 d.limb1.val :=
    stepDigit_segment d 1 31 (by decide)
  have s2 : (List.range' 62 31).map (stepDigit d) = extractLimbBase4Digits 31 d.limb2.val :=
    stepDigit_segment d 2 31 (by decide)
  have s3 : (List.range' 93 31).map (stepDigit d) = extractLimbBase4Digits 31 d.limb3.val :=
    stepDigit_segment d 3 31 (by decide)
  have s4 : (List.range' 124 4).map (stepDigit d) = extractLimbBase4Digits 4 d.limb4.val :=
    stepDigit_segment d 4 4 (by decide)
  simp only [extractWotsDigitsChecked.public_eqs]
  rw [hChk, range'_128_split, List.map_append, List.map_append, List.map_append,
    List.map_append, s0, s1, s2, s3, s4, hw]
  simp only [↓reduceIte]
  rw [List.take_of_length_le (by simp [extractLimbBase4Digits_length])]

/-! ### §3.12. One full layer: digits, WOTS+C and Merkle rows give `verifyWotsLayer` -/

theorem mem_range'_of_bounds : ∀ (n s c : Nat), s ≤ c → c < s + n → c ∈ List.range' s n
  | 0, _, _, _, _ => by omega
  | n + 1, s, c, h1, h2 => by
    have e : List.range' s (n + 1) = s :: List.range' (s + 1) n := rfl
    rw [e, List.mem_cons]
    by_cases hc : c = s
    · exact .inl hc
    · exact .inr (mem_range'_of_bounds n (s + 1) c (by omega) (by omega))

theorem recoverAggWotsEndpoints_map (pkSeed : Lane4) (layer tree kpN : Nat)
    (dg : Nat → Nat) (a : Nat → Lane4) :
    ∀ (n c0 : Nat),
      recoverAggWotsEndpoints pkSeed layer tree kpN c0 ((List.range' c0 n).map dg)
          ((List.range' c0 n).map a) =
        (List.range' c0 n).map
          (fun c => wotsChainWalk pkSeed layer tree kpN c (dg c) (3 - dg c) (a c))
  | 0, _ => by simp only [List.range'_zero, List.map_nil,
      recoverAggWotsEndpoints.public_eqs, recoverEndpointsPoly.public_eqs]
  | n + 1, c0 => by
    have e : List.range' c0 (n + 1) = c0 :: List.range' (c0 + 1) n := rfl
    rw [e, List.map_cons, List.map_cons, List.map_cons,
      ← recoverAggWotsEndpoints_map pkSeed layer tree kpN dg a n (c0 + 1)]
    simp only [recoverAggWotsEndpoints.public_eqs, recoverEndpointsPoly.public_eqs]

theorem stepWotsOps_length (layer : Nat) : (stepWotsOps layer).length = 450 := by
  unfold stepWotsOps
  rw [List.length_append, List.length_append, flatMap_range_uniform_length _ 7 (fun _ => rfl)]
  rfl

/-- The 128 signature chain values read from the `WotsChainStep0` rows of a layer. -/
@[expose] def stepLayerChains (R : Nat → StepOpRow) (t0 : Nat) : List Lane4 :=
  (List.range 128).map fun c => stepAuxLane R (stepChainRow t0 c) 0

/-- The authentication path read from the `XmssMerkleBlockA` rows starting at row `t1`. -/
@[expose] def stepLayerPath (R : Nat → StepOpRow) (t1 h : Nat) : List Lane4 :=
  (List.range h).map fun l => stepAuxLane R (t1 + 2 * l) 2

/-- **Layer rows.** Five `HmsgDecompLimb` rows followed by `pushLayerWotsAndMerkle` verify one
    WOTS+C layer: with the digest in `ST_MAIN_SPONGE`, the native `verifyWotsLayer` accepts the
    chain values and authentication path read from the auxiliary columns, and returns the
    permutation output of the last `XmssMerkleBlockB` row. -/
theorem stepLayer_verify {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {geom : AggSigGeometry} {layer h tD kpN tree ctr : Nat} {isTop : Bool}
    (hDec : StepRunAt pub R ((List.range 5).map StepOp.hmsgDecompLimb) tD)
    (hLayer : StepRunAt pub R (pushLayerWotsAndMerkle layer h isTop) (tD + 5))
    (hRem0 : ∀ s < 6, (stepRegsAt R tD).rem.get s = Goldilocks.zero)
    (hAcc0 : (stepRegsAt R tD).acc = Goldilocks.zero)
    (hAddr : StepAddrOk (stepRegsAt R tD) kpN tree)
    (hLastIn : (R (tD + 455 + 2 * (h - 1) + 1)).stIn =
      stepMerkleBIn (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)))
    (hLastCur : (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)).cursor = Goldilocks.zero)
    (hl : layer < 64) (hk : kpN < 2 ^ 28) (hh : 0 < h) (hh28 : h ≤ 28)
    (hw : geom.wotsChains = 128) (hts : geom.targetSum = 192) (hsh : geom.subtreeHeight = h) :
    kpN < 2 ^ h ∧
    verifyWotsLayer geom pub.1 layer tree kpN (stepHmsgOf (stepRegsAt R tD).main)
        ⟨ctr, stepLayerChains R (tD + 5), stepLayerPath R (tD + 455) h⟩ =
      some (stepPermAt R (tD + 455 + 2 * (h - 1) + 1)).b0 ∧
    (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)).curRoot = (stepRegsAt R tD).curRoot ∧
    StepAddrOk (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)) kpN tree := by
  obtain ⟨hChk, hPack, hSum, _, hCR, hKp, hLo, hHi⟩ := stepDecomp_sem hDec hRem0 hAcc0
  obtain ⟨hm, hhm⟩ : ∃ hm, hm = stepHmsgOf (stepRegsAt R tD).main := ⟨_, rfl⟩
  rw [← hhm] at hChk hPack hSum ⊢
  have hAddr5 : StepAddrOk (stepRegsAt R (tD + 5)) kpN tree :=
    ⟨hKp.trans hAddr.kp, hLo.trans hAddr.lo, hHi.trans hAddr.hi⟩
  rw [pushLayerWotsAndMerkle_eq] at hLayer
  have e450 : tD + 5 + 450 = tD + 455 := by omega
  have hM : StepRunAt pub R (stepMerkleOps layer h isTop) (tD + 455) := by
    have h' := hLayer.append_right
    rw [stepWotsOps_length, e450] at h'
    exact h'
  obtain ⟨hd, hSlots, hWork, hCur450R, hAddr450, hCursor⟩ :=
    stepWots_sem hLayer.append_left hAddr5 hl hk
  rw [e450] at hWork hCur450R hAddr450 hCursor
  have hDigEq : ∀ s a len : Nat, (∀ c < 128, wotsPackSlot c = s ↔ a ≤ c ∧ c < a + len) → s < 5 →
      a + len ≤ 128 → 4 ^ len < goldilocksPrime → wotsPackSlotStart s = a →
      ∀ c, a ≤ c → c < a + len →
        stepChainDigit R (stepChainRow (tD + 5) c) = stepDigit hm c := by
    intro s a len hRange hs haN hLen hStart c hac hcl
    have h1 := hSlots s a len hRange hs haN hLen
    have h2 := hPack s (by omega)
    rw [stepPackFold_slot _ s a len hRange haN hStart] at h2
    rw [h2] at h1
    have hLtD : ∀ x ∈ (List.range' a len).map (fun c => 3 - stepDigit hm c), x < 4 := by
      intro x hx
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
      show 3 - stepDigit hm c' < 4
      omega
    have hLtd : ∀ x ∈ (List.range' a len).map
        (fun c => 3 - stepChainDigit R (stepChainRow (tD + 5) c)), x < 4 := by
      intro x hx
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
      show 3 - stepChainDigit R (stepChainRow (tD + 5) c') < 4
      omega
    have hBound := evalBaseDigits_lt_pow 4 (by decide) _ hLtD
    rw [List.length_map, List.length_range'] at hBound
    rw [Goldilocks.ofNat_val, Nat.mod_eq_of_lt (Nat.lt_trans hBound hLen)] at h1
    have hList := evalBaseDigits_inj 4 (by decide)
      (by rw [List.length_map, List.length_map]) hLtD hLtd h1
    have hc : 3 - stepDigit hm c = 3 - stepChainDigit R (stepChainRow (tD + 5) c) :=
      (List.map_inj_left.mp hList) c (mem_range'_of_bounds len a c hac hcl)
    have hd1 := hd c (by omega)
    have hd2 := stepDigit_le hm c
    omega
  have hDigAll : ∀ c < 128, stepChainDigit R (stepChainRow (tD + 5) c) = stepDigit hm c := by
    intro c hc
    by_cases h0 : c < 26
    · exact hDigEq 0 0 26 wotsPackSlot_range0 (by decide) (by decide) (by decide) (by simp only [wotsPackSlotStart.public_eqs]) c
        (by omega) (by omega)
    by_cases h1 : c < 52
    · exact hDigEq 1 26 26 wotsPackSlot_range1 (by decide) (by decide) (by decide) (by simp only [wotsPackSlotStart.public_eqs]) c
        (by omega) (by omega)
    by_cases h2 : c < 78
    · exact hDigEq 2 52 26 wotsPackSlot_range2 (by decide) (by decide) (by decide) (by simp only [wotsPackSlotStart.public_eqs]) c
        (by omega) (by omega)
    by_cases h3 : c < 103
    · exact hDigEq 3 78 25 wotsPackSlot_range3 (by decide) (by decide) (by decide) (by simp only [wotsPackSlotStart.public_eqs]) c
        (by omega) (by omega)
    · exact hDigEq 4 103 25 wotsPackSlot_range4 (by decide) (by decide) (by decide) (by simp only [wotsPackSlotStart.public_eqs]) c
        (by omega) (by omega)
  have hEnd : stepLayerEndpoints pub R layer tree kpN (tD + 5) =
      recoverAggWotsEndpoints pub.1.pkSeed layer tree kpN 0
        ((List.range' 0 128).map (stepDigit hm)) (stepLayerChains R (tD + 5)) := by
    unfold stepLayerEndpoints stepLayerChains
    rw [List.range_eq_range', recoverAggWotsEndpoints_map]
    apply List.map_congr_left
    intro c hc
    have hb := mem_range'_bounds _ _ _ hc
    unfold stepChainEndpoint
    rw [hDigAll c (by omega)]
  have hLv : ∀ l < h, StepRunAt pub R
      [StepOp.xmssMerkleBlockA layer l,
       StepOp.xmssMerkleBlockB (l + 1 == h) ((l + 1 == h) && isTop)] (tD + 455 + l * 2) :=
    StepRunAt.flatMap_range (L := 2) (fun _ => rfl) h hM
  have hA : ∀ l < h, StepRowSem pub R (.xmssMerkleBlockA layer l) (tD + 455 + 2 * l) := by
    intro l hl'
    have h' := (hLv l hl').head
    rw [Nat.mul_comm l 2] at h'
    exact h'
  have hB : ∀ l < h, StepRowSem pub R
      (.xmssMerkleBlockB (l + 1 == h) ((l + 1 == h) && isTop)) (tD + 455 + 2 * l + 1) := by
    intro l hl'
    have h' := (hLv l hl').tail.head
    rw [Nat.mul_comm l 2] at h'
    exact h'
  have hBin : ∀ l < h, (R (tD + 455 + 2 * l + 1)).stIn =
      stepMerkleBIn (stepRegsAt R (tD + 455 + 2 * l + 1)) := by
    intro l hl'
    by_cases hlast : l + 1 < h
    · have hb : (l + 1 == h) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hB' := hB l hl'
      rw [hb] at hB'
      exact (stepSem_xmssMerkleBlockB_inner hB').1
    · have e : l = h - 1 := by omega
      rw [e]
      exact hLastIn
  have hBnext : ∀ l, l + 1 < h → stepRegsAt R (tD + 455 + 2 * l + 2) =
      { stepRegsAt R (tD + 455 + 2 * l + 1) with
        work := (stepPermAt R (tD + 455 + 2 * l + 1)).b0 } := by
    intro l hl'
    have hb : (l + 1 == h) = false := beq_eq_false_iff_ne.mpr (by omega)
    have hB' := hB l (by omega)
    rw [hb] at hB'
    exact (stepSem_xmssMerkleBlockB_inner hB').2
  obtain ⟨hKpLt, hWalk, hFr⟩ :=
    stepMerkle_sem (tag := domainMerkleNode)
      (M := fun l => ‹layer * 2 ^ 48 + (l + 1) * 2 ^ 32›) (layerV := layer) (treeV := tree)
      (addr := xmssNodeAddr) (fun l hl' => stepMerkleARow_xmss (hA l hl')) hBin hBnext hLastCur
      hCursor hk hh hh28 (fun l hl' _ L Rr => by
        rw [hAddr450.lo, hAddr450.hi]
        exact stepNodeHashF_xmss _ _ _ _ _ _ _ (by omega) (by omega)
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans hk (by decide))))
  refine ⟨hKpLt, ?_, hFr.curRoot.trans (hCur450R.trans hCR),
    ⟨hFr.kp.trans hAddr450.kp, hFr.treeLo.trans hAddr450.lo, hFr.treeHi.trans hAddr450.hi⟩⟩
  have hLen1 : (stepLayerChains R (tD + 5)).length = 128 := by
    unfold stepLayerChains
    rw [List.length_map, List.length_range]
  have hLen2 : (stepLayerPath R (tD + 455) h).length = h := by
    unfold stepLayerPath
    rw [List.length_map, List.length_range]
  simp only [verifyWotsLayer.public_eqs]
  simp only [hLen1, hLen2, hw, hsh, beq_self_eq_true, Bool.and_self, ↓reduceIte,
    stepDigits_extract geom hm hw hChk, hSum, hts]
  rw [← hEnd, ← hWork]
  exact congrArg some hWalk

/-! ### §3.13. Active `XmssPoseidon2` slot: an accepted table yields a native signature -/

/-- `Σ_{i < n} (f i).val * w i`, the integer read off a weighted sum of cells. -/
@[expose] def stepWeightedNat (f : Nat → Goldilocks) (w : Nat → Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + (f i).val * w i) 0

private theorem stepWeightedSum_fold (f : Nat → Goldilocks) (w : Nat → Nat) :
    ∀ (is : List Nat) (A : Nat),
      is.foldl (fun acc i => acc +ₚ (f i *ₚ ‹w i›)) ‹A› =
        ‹is.foldl (fun acc i => acc + (f i).val * w i) A›
  | [], _ => rfl
  | i :: rest, A => by
    have hStep : (‹A› : Goldilocks) +ₚ (f i *ₚ ‹w i›) = ‹A + (f i).val * w i› := by
      rw [g_ofNat_add, g_ofNat_mul, g_ofNat_self]
    rw [List.foldl_cons, List.foldl_cons, hStep]
    exact stepWeightedSum_fold f w rest _

theorem stepWeightedSum_eq_ofNat (f : Nat → Goldilocks) (w : Nat → Nat) (n : Nat) :
    stepWeightedSum f w n = ‹stepWeightedNat f w n› := by
  rw [stepWeightedSum_eq]
  exact stepWeightedSum_fold f w (List.range n) 0

theorem stepWeightedNat_succ (f : Nat → Goldilocks) (w : Nat → Nat) (n : Nat) :
    stepWeightedNat f w (n + 1) = stepWeightedNat f w n + (f n).val * w n := by
  unfold stepWeightedNat
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem stepWeightedNat_bits_lt (f : Nat → Goldilocks) :
    ∀ (n : Nat), (∀ i < n, f i = Goldilocks.zero ∨ f i = Goldilocks.one) →
      stepWeightedNat f (fun i => 2 ^ i) n < 2 ^ n
  | 0, _ => Nat.le_of_ble_eq_true rfl
  | n + 1, h => by
    have ih := stepWeightedNat_bits_lt f n (fun i hi => h i (by omega))
    have hb : (f n).val ≤ 1 := by
      rcases h n (by omega) with hb | hb <;> rw [hb] <;> decide
    have hm : (f n).val * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ hb
    rw [stepWeightedNat_succ, Nat.pow_succ]
    omega

theorem verifyUpperLayers_nil (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer rem : Nat) (root : Digest4) :
    verifyUpperLayers geom pk layer rem root [] = some root := by
  simp only [verifyUpperLayers.public_eqs, verifyUpperPoly.public_eqs]

/-- A stateful single-layer signature is accepted once its layer verifies to the root. -/
theorem verifyAggNativeSig_stateful_intro (geom : AggSigGeometry) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (leaf : Nat) (lsig0 : WotsLayerSig)
    (hWf : geom.wellFormed = true) (hPk : pk.profile = geom.profile)
    (hNL : geom.numLayers = 1) (hF : geom.forsTrees = 0)
    (hLeaf : leaf < 2 ^ (geom.numLayers * geom.subtreeHeight))
    (hV : verifyWotsLayer geom pk 0 (leaf / 2 ^ geom.subtreeHeight)
        (leaf % 2 ^ geom.subtreeHeight)
        (computeHmsgStateful pk rRand (computeMessageMu pk msg)
          (leaf % 2 ^ geom.subtreeHeight) lsig0.tswCtr) lsig0 = some pk.pkRoot) :
    verifyAggNativeSig geom pk msg ⟨geom.profile, rRand, leaf, [], [lsig0]⟩ = true := by
  have hCond : (!geom.wellFormed || pk.profile != geom.profile ||
      geom.profile != geom.profile || ([lsig0].length != geom.numLayers)) = false := by
    rw [hWf, hPk, hNL]
    simp
  have hDec : (!([] : List AggForsTreeOpening).isEmpty ||
      !decide (leaf < 2 ^ (geom.numLayers * geom.subtreeHeight))) = false := by
    simp [hLeaf]
  simp only [verifyAggNativeSig.public_eqs]
  simp only [hCond, Bool.false_eq_true, ↓reduceIte, hF, beq_self_eq_true]
  simp only [verifyAggNativeSigStateful.public_eqs]
  simp only [hDec, Bool.false_eq_true, ↓reduceIte, hV, verifyUpperLayers_nil, beq_self_eq_true]

/-- The native signature read from the auxiliary columns of an `XmssPoseidon2` signer block:
    `rRand` from the `StatefulHmsgBlock1` row, the leaf index and counter bits from the
    `StatefulHmsgBlock0` row, the chain values from the `WotsChainStep0` rows and the
    authentication path from the `XmssMerkleBlockA` rows. -/
@[expose] def stepXmssSig (R : Nat → StepOpRow) : AggNativeSignature :=
  { profile := .xmssPoseidon2
    rRand := stepAuxLane R 1 0
    statefulLeafIdx := stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6
    forsOpenings := []
    layers :=
      [⟨stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32,
        stepLayerChains R 8, stepLayerPath R 458 6⟩] }

/-- **Native-signature witness extraction, `XmssPoseidon2` profile.** If the 256-column `StepOp`
    table is accepted and slot `k` is active with public inputs `(pk, mu)`, `mu` the message
    representative of `msg` under `pk`, then the signature read from the auxiliary columns of
    the slot's rows is accepted by the native verifier. -/
theorem stepOp256TableOk_xmss_extract (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hTable : stepOp256TableOk .xmssPoseidon2 slots rows = true)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .xmssPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    verifyAggNativeSig xmssPoseidon2Geom pub.1 msg
      (stepXmssSig (stepOpSlotRow .xmssPoseidon2 rows k)) = true := by
  obtain ⟨R, hR⟩ : ∃ R, R = stepOpSlotRow .xmssPoseidon2 rows k := ⟨_, rfl⟩
  rw [← hR]
  have hRun0 := stepOp256TableOk_slot_run .xmssPoseidon2 slots rows k pub hTable hSlot
  rw [← hR] at hRun0
  have hInit := stepOp256TableOk_slot_init .xmssPoseidon2 slots rows k pub hTable hSlot
  rw [← hR] at hInit
  have hRun : StepRunAt pub R
      (([StepOp.statefulHmsgBlock0, StepOp.statefulHmsgBlock1, StepOp.statefulHmsgSqueeze] ++
        (List.range 5).map StepOp.hmsgDecompLimb) ++ pushLayerWotsAndMerkle 0 6 true) 0 := by
    simpa only [signerProgramBody.public_eqs] using hRun0
  have h0 : StepRowSem pub R .statefulHmsgBlock0 0 := hRun.append_left.append_left.head
  have h1 : StepRowSem pub R .statefulHmsgBlock1 1 := hRun.append_left.append_left.tail.head
  have h2 : StepRowSem pub R .statefulHmsgSqueeze 2 :=
    hRun.append_left.append_left.tail.tail.head
  have hDec : StepRunAt pub R ((List.range 5).map StepOp.hmsgDecompLimb) 3 :=
    hRun.append_left.append_right
  have hLayer : StepRunAt pub R (pushLayerWotsAndMerkle 0 6 true) (3 + 5) := hRun.append_right
  have hTop : StepRowSem pub R (.xmssMerkleBlockB true true) 469 :=
    StepRunAt.get hRun0 469 _ signerProgramBody_xmss_last
  obtain ⟨hb6, hb32, hIn0, hR1⟩ := stepSem_statefulHmsgBlock0 h0
  obtain ⟨hIn1, hR2⟩ := stepSem_statefulHmsgBlock1 h1
  obtain ⟨hIn2, hR3⟩ := stepSem_statefulHmsgSqueeze h2
  have hR1' : stepRegsAt R 1 = _ := hR1
  have hR2' : stepRegsAt R 2 = _ := hR2
  have hR3' : stepRegsAt R 3 = _ := hR3
  obtain ⟨hLastIn, hLastCur, hRoot⟩ := stepSem_xmssMerkleBlockB_top hTop
  have hKp6 := stepWeightedNat_bits_lt (stepAux R 0) 6 hb6
  have hCtr := stepWeightedNat_bits_lt (fun i => stepAux R 0 (6 + i)) 32 hb32
  have hRem0 : ∀ s < 6, (stepRegsAt R 3).rem.get s = Goldilocks.zero := by
    intro s hs
    rw [hR3']
    rcases s with _ | _ | _ | _ | _ | _ | s
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hs (by omega)
  have hAcc0 : (stepRegsAt R 3).acc = Goldilocks.zero := by rw [hR3']
  have hAddr : StepAddrOk (stepRegsAt R 3)
      (stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6) 0 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hR3', hR2', hR1']
      exact stepWeightedSum_eq_ofNat _ _ _
    · rw [hR3', hR2', hR1']
      exact Goldilocks.ext rfl
    · rw [hR3', hR2', hR1']
      exact Goldilocks.ext rfl
  have hHm : stepHmsgOf (stepRegsAt R 3).main =
      computeHmsgStateful pub.1 (stepAuxLane R 1 0) pub.2
        (stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6)
        (stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32) := by
    have hKpCtr : (stepWeightedSum (stepAux R 0) (fun i => 2 ^ i) 6 *ₚ ‹2 ^ 32›) +ₚ
        stepWeightedSum (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32 =
        ‹(stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6 % 2 ^ 32) * 2 ^ 32 +
          stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32 % 2 ^ 32› := by
      rw [stepWeightedSum_eq_ofNat, stepWeightedSum_eq_ofNat, ← g_ofNat_mul, ← g_ofNat_add,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hCtr]
    have hM1 : (stepRegsAt R 1).main = poseidon2Perm12 (R 0).stIn := by rw [hR1']; rfl
    have hM2 : (stepRegsAt R 2).main = poseidon2Perm12 (R 1).stIn := by rw [hR2']; rfl
    have hM3 : (stepRegsAt R 3).main = poseidon2Perm12 (R 2).stIn := by rw [hR3']; rfl
    rw [hM3, hIn2]
    unfold stepSqueezeIn
    rw [hM2, hIn1, hM1, hIn0, hKpCtr]
    simp only [computeHmsgStateful.public_eqs, stepHmsgOf]
  obtain ⟨hKpLt, hV, _, _⟩ := stepLayer_verify (geom := xmssPoseidon2Geom) (layer := 0) (h := 6)
    (ctr := stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32)
    hDec hLayer hRem0 hAcc0 hAddr hLastIn hLastCur (by decide) (by omega) (by decide) (by decide)
    (by simp only [xmssPoseidon2Geom.public_eqs])
    (by simp only [xmssPoseidon2Geom.public_eqs])
    (by simp only [xmssPoseidon2Geom.public_eqs])
  rw [hHm, hMu] at hV
  have hV' : verifyWotsLayer xmssPoseidon2Geom pub.1 0 0
      (stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6)
      (computeHmsgStateful pub.1 (stepAuxLane R 1 0) (computeMessageMu pub.1 msg)
        (stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6)
        (stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32))
      ⟨stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32,
        stepLayerChains R 8, stepLayerPath R 458 6⟩ = some pub.1.pkRoot := by
    rw [← hRoot]
    exact hV
  have hDiv : stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6 /
      2 ^ xmssPoseidon2Geom.subtreeHeight = 0 := by
    simpa only [xmssPoseidon2Geom.public_eqs] using Nat.div_eq_of_lt hKp6
  have hMod : stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6 %
      2 ^ xmssPoseidon2Geom.subtreeHeight =
      stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6 := by
    simpa only [xmssPoseidon2Geom.public_eqs] using Nat.mod_eq_of_lt hKp6
  simpa only [stepXmssSig,
    show xmssPoseidon2Geom.profile = AggSigProfile.xmssPoseidon2 by
      simp only [xmssPoseidon2Geom.public_eqs]] using
    verifyAggNativeSig_stateful_intro xmssPoseidon2Geom pub.1 msg (stepAuxLane R 1 0)
    (stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6)
    ⟨stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32,
      stepLayerChains R 8, stepLayerPath R 458 6⟩
    (by simp only [xmssPoseidon2Geom.public_eqs]; decide +kernel)
    (by simpa only [xmssPoseidon2Geom.public_eqs] using hProf)
    (by simp only [xmssPoseidon2Geom.public_eqs])
    (by simp only [xmssPoseidon2Geom.public_eqs])
    (by simpa only [xmssPoseidon2Geom.public_eqs] using hKp6)
    (by rw [hDiv, hMod]; exact hV')

end HemStepOp256Machine
end Qsag
end

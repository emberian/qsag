module
/-
# WOTS+C Chain Rows, Chain Pairs, `ST_REM_PACK` Bookkeeping, and the Subtree Merkle Path

Three guarded rows walk one WOTS+C chain; one chain pair walks two chains and absorbs them into
the sponge; the chain rows unpack exactly the packed digits of `ST_REM_PACK`; the WOTS+C part of
one layer recovers its endpoints; and the subtree Merkle rows of one layer walk the
authentication path.
-/

public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.StepOp256RowSemantics

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

/-! ### §3.6. WOTS+C chain rows: three guarded rows walk one chain -/

/-- The address registers hold key-pair index `kpN` and the two 32-bit halves of `tree`. -/
structure StepAddrOk (r : StepRegs) (kpN tree : Nat) : Prop where
  kp : r.kp = ‹kpN›
  lo : r.treeLo = ‹tree % 2 ^ 32›
  hi : r.treeHi = ‹(tree / 2 ^ 32) % 2 ^ 32›

/-- Number of skipped chain steps `u0 + u1 + u2` of the `WotsChainStep0` row `t`. -/
def stepChainDigit (R : Nat → StepOpRow) (t : Nat) : Nat :=
  (stepAux R t 4).val + (stepAux R t 5).val + (stepAux R t 6).val

private def stepChainIter (F0 F1 F2 : Lane4 → Lane4) : Nat → Lane4 → Lane4
  | 0, a => F2 (F1 (F0 a))
  | 1, a => F2 (F1 a)
  | 2, a => F2 a
  | _, a => a

private theorem stepChainMux_eq (F0 F1 F2 : Lane4 → Lane4) (u0 u1 u2 : Goldilocks) (a : Lane4)
    (hb0 : u0 = Goldilocks.zero ∨ u0 = Goldilocks.one)
    (hb1 : u1 = Goldilocks.zero ∨ u1 = Goldilocks.one)
    (hb2 : u2 = Goldilocks.zero ∨ u2 = Goldilocks.one)
    (hm1 : u1 *ₚ (Goldilocks.one -ₚ u0) = Goldilocks.zero)
    (hm2 : u2 *ₚ (Goldilocks.one -ₚ u1) = Goldilocks.zero) :
    u0.val + u1.val + u2.val ≤ 3 ∧
    (‹3› -ₚ ((u0 +ₚ u1) +ₚ u2)) = ‹3 - (u0.val + u1.val + u2.val)› ∧
    lane4Mux u2 (lane4Mux u1 (lane4Mux u0 a (F0 a)) (F1 (lane4Mux u0 a (F0 a))))
        (F2 (lane4Mux u1 (lane4Mux u0 a (F0 a)) (F1 (lane4Mux u0 a (F0 a))))) =
      stepChainIter F0 F1 F2 (u0.val + u1.val + u2.val) a := by
  rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl
  all_goals first
    | exact absurd hm1 (by decide +kernel)
    | exact absurd hm2 (by decide +kernel)
    | (refine ⟨by decide, by decide +kernel, ?_⟩
       simp only [lane4Mux_one, lane4Mux_zero]
       rfl)

private theorem stepChainIter_walk (pkSeed : Lane4) (layer tree kpN chain d : Nat) (a : Lane4)
    (hd : d ≤ 3) :
    stepChainIter (fun v => wotsStepHash pkSeed v layer tree kpN chain 0)
        (fun v => wotsStepHash pkSeed v layer tree kpN chain 1)
        (fun v => wotsStepHash pkSeed v layer tree kpN chain 2) d a =
      wotsChainWalk pkSeed layer tree kpN chain d (3 - d) a := by
  rcases d with _ | _ | _ | _ | d
  all_goals first
    | omega
    | simp only [stepChainIter, Nat.reduceSub, Nat.reduceAdd,
        wotsChainWalk_succ_steps, wotsChainWalk_zero_steps]

private theorem stepWotsHash_eq {R : Nat → StepOpRow} {t : Nat} {r : StepRegs}
    {pkSeed cur : Lane4} {c0 layer chain k kpN tree : Nat}
    (hIn : (R t).stIn = ⟨cur, pkSeed, stepWotsTweak r c0⟩) (hAddr : StepAddrOk r kpN tree)
    (hc0 : c0 = layer * 2 ^ 44 + chain * 2 ^ 4 + k)
    (hl : layer < 64) (hk : kpN < 2 ^ 28) (hc : chain < 4096) (hk16 : k < 16) :
    stepFfAt R t cur = wotsStepHash pkSeed cur layer tree kpN chain k := by
  have hT : stepWotsTweak r c0 =
      ⟨domainWotsStep, packWotsAddrLimb layer kpN chain k, ‹tree % 2 ^ 32›,
        ‹(tree / 2 ^ 32) % 2 ^ 32›⟩ := by
    simp only [stepWotsTweak.public_eqs, packWotsAddrLimb.public_eqs]
    rw [hAddr.kp, hAddr.lo, hAddr.hi, ← g_ofNat_mul, ← g_ofNat_add, hc0,
      Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hk16]
    have e : layer * 2 ^ 44 + chain * 2 ^ 4 + k + kpN * 2 ^ 16 =
        layer * 2 ^ 44 + kpN * 2 ^ 16 + chain * 16 + k := by omega
    rw [e]
  simp only [stepFfAt.public_eqs, stepPermAt, wotsStepHash.public_eqs, poseidon2Compress12FF.public_eqs, poseidon2CompressWeighted_eq]
  rw [hIn, hT]

/-- **Chain rows.** The three rows of one WOTS+C chain shift the remaining-step count
    `3 - d` out of the chain's `ST_REM_PACK` limb and leave `wotsChainWalk` of the signature
    value from step `d` in `ST_WORK` (odd chain) or `ST_SUB_SPONGE[0..4]` (even chain). -/
theorem stepChain_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer chain slot t kpN tree : Nat} {odd : Bool}
    (h0 : StepRowSem pub R (.wotsChainStep0 layer chain slot) t)
    (h1 : StepRowSem pub R (.wotsChainStep1 layer chain) (t + 1))
    (h2 : StepRowSem pub R (.wotsChainStep2 layer chain odd) (t + 2))
    (hs : slot < 6) (hAddr : StepAddrOk (stepRegsAt R t) kpN tree)
    (hl : layer < 64) (hk : kpN < 2 ^ 28) (hc : chain < 4096) :
    stepChainDigit R t ≤ 3 ∧
    (stepRegsAt R t).rem.get slot =
      ‹3 - stepChainDigit R t› +ₚ (stepAux R t 7 *ₚ ‹4›) ∧
    ∃ (W : Lane4) (A U : Goldilocks), stepRegsAt R (t + 3) =
      { stepRegsAt R t with
        rem := (stepRegsAt R t).rem.set slot (stepAux R t 7)
        sub := if odd then (stepRegsAt R t).sub else
          ⟨wotsChainWalk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
              (3 - stepChainDigit R t) (stepAuxLane R t 0),
            (stepRegsAt R t).sub.b1, (stepRegsAt R t).sub.b2⟩
        work := if odd then
            wotsChainWalk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
              (3 - stepChainDigit R t) (stepAuxLane R t 0)
          else W
        acc := A
        u2 := U } := by
  obtain ⟨hb0, hb1, hb2, hm1, hm2, hRem, hIn0, hR1⟩ := stepSem_wotsChainStep0 hs h0
  obtain ⟨hIn1, hR2⟩ := stepSem_wotsChainStep1 h1
  have hR2' : stepRegsAt R (t + 2) = _ := hR2
  have hA1 : StepAddrOk (stepRegsAt R (t + 1)) kpN tree := by
    rw [hR1]; exact ⟨hAddr.kp, hAddr.lo, hAddr.hi⟩
  have hA2 : StepAddrOk (stepRegsAt R (t + 2)) kpN tree := by
    rw [hR2']; exact ⟨hA1.kp, hA1.lo, hA1.hi⟩
  have e0 := stepWotsHash_eq (k := 0) (c0 := layer * 2 ^ 44 + chain * 2 ^ 4) hIn0 hAddr
    (Nat.add_zero _).symm hl hk hc (by decide)
  have e1 := stepWotsHash_eq (k := 1) (c0 := layer * 2 ^ 44 + chain * 2 ^ 4 + 1) hIn1 hA1
    (Eq.refl _) hl hk hc (by decide)
  have hw1 : (stepRegsAt R (t + 1)).work =
      lane4Mux (stepAux R t 4) (stepAuxLane R t 0)
        (wotsStepHash pub.1.pkSeed (stepAuxLane R t 0) layer tree kpN chain 0) := by
    rw [hR1, ← e0]
  have hacc1 : (stepRegsAt R (t + 1)).acc = stepAux R t 5 := by rw [hR1]
  have hu1 : (stepRegsAt R (t + 1)).u2 = stepAux R t 6 := by rw [hR1]
  have hw2 : (stepRegsAt R (t + 2)).work =
      lane4Mux (stepAux R t 5)
        (lane4Mux (stepAux R t 4) (stepAuxLane R t 0)
          (wotsStepHash pub.1.pkSeed (stepAuxLane R t 0) layer tree kpN chain 0))
        (wotsStepHash pub.1.pkSeed
          (lane4Mux (stepAux R t 4) (stepAuxLane R t 0)
            (wotsStepHash pub.1.pkSeed (stepAuxLane R t 0) layer tree kpN chain 0))
          layer tree kpN chain 1) := by
    rw [hR2']
    show lane4Mux (stepRegsAt R (t + 1)).acc (stepRegsAt R (t + 1)).work
      (stepFfAt R (t + 1) (stepRegsAt R (t + 1)).work) = _
    rw [e1, hacc1, hw1]
  have hu2 : (stepRegsAt R (t + 2)).u2 = stepAux R t 6 := by
    rw [hR2']; exact hu1
  obtain ⟨hd, hThree, hIter⟩ := stepChainMux_eq
    (fun v => wotsStepHash pub.1.pkSeed v layer tree kpN chain 0)
    (fun v => wotsStepHash pub.1.pkSeed v layer tree kpN chain 1)
    (fun v => wotsStepHash pub.1.pkSeed v layer tree kpN chain 2)
    (stepAux R t 4) (stepAux R t 5) (stepAux R t 6) (stepAuxLane R t 0) hb0 hb1 hb2 hm1 hm2
  have hWalk := stepChainIter_walk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
    (stepAuxLane R t 0) hd
  refine ⟨hd, ?_, (stepRegsAt R (t + 2)).work, (stepRegsAt R (t + 2)).acc,
    (stepRegsAt R (t + 2)).u2, ?_⟩
  · rw [hRem, hThree]
    rfl
  · cases odd
    · obtain ⟨hIn2, hR3⟩ := stepSem_wotsChainStep2_even h2
      have hR3' : stepRegsAt R (t + 3) = _ := hR3
      have e2 := stepWotsHash_eq (k := 2) (c0 := layer * 2 ^ 44 + chain * 2 ^ 4 + 2) hIn2 hA2
        (Eq.refl _) hl hk hc (by decide)
      have hX : lane4Mux (stepRegsAt R (t + 2)).u2 (stepRegsAt R (t + 2)).work
          (stepFfAt R (t + 2) (stepRegsAt R (t + 2)).work) =
          wotsChainWalk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
            (3 - stepChainDigit R t) (stepAuxLane R t 0) := by
        rw [e2, hu2, hw2, ← hWalk]
        exact hIter
      rw [hR3', hX, hR2', hR1]
      rfl
    · obtain ⟨hIn2, hR3⟩ := stepSem_wotsChainStep2_odd h2
      have hR3' : stepRegsAt R (t + 3) = _ := hR3
      have e2 := stepWotsHash_eq (k := 2) (c0 := layer * 2 ^ 44 + chain * 2 ^ 4 + 2) hIn2 hA2
        (Eq.refl _) hl hk hc (by decide)
      have hX : lane4Mux (stepRegsAt R (t + 2)).u2 (stepRegsAt R (t + 2)).work
          (stepFfAt R (t + 2) (stepRegsAt R (t + 2)).work) =
          wotsChainWalk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
            (3 - stepChainDigit R t) (stepAuxLane R t 0) := by
        rw [e2, hu2, hw2, ← hWalk]
        exact hIter
      rw [hR3', hX, hR2', hR1]
      rfl

/-! ### §3.7. One chain pair: two chains and their sponge absorption -/

/-- The seven opcodes of chain pair `pair` of a WOTS+C layer. -/
@[expose] def stepPairOps (layer pair : Nat) : List StepOp :=
  (List.range 2).flatMap (fun sub =>
      [StepOp.wotsChainStep0 layer (2 * pair + sub) (wotsPackSlot (2 * pair + sub)),
       StepOp.wotsChainStep1 layer (2 * pair + sub),
       StepOp.wotsChainStep2 layer (2 * pair + sub) (sub == 1)]) ++
    [StepOp.wotsTellPairAbsorb pair]

/-- Endpoint recovered by the chain whose `WotsChainStep0` row is `t`. -/
@[expose] def stepChainEndpoint (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (layer tree kpN chain t : Nat) : Lane4 :=
  wotsChainWalk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
    (3 - stepChainDigit R t) (stepAuxLane R t 0)

/-- What the seven rows of one chain pair starting at row `T` establish. -/
structure StepPairFacts (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (layer kpN tree pair T : Nat) : Prop where
  dE : stepChainDigit R T ≤ 3
  dO : stepChainDigit R (T + 3) ≤ 3
  getE : (stepRegsAt R T).rem.get (wotsPackSlot (2 * pair)) =
    ‹3 - stepChainDigit R T› +ₚ (stepAux R T 7 *ₚ ‹4›)
  setE : (stepRegsAt R (T + 3)).rem =
    (stepRegsAt R T).rem.set (wotsPackSlot (2 * pair)) (stepAux R T 7)
  getO : (stepRegsAt R (T + 3)).rem.get (wotsPackSlot (2 * pair + 1)) =
    ‹3 - stepChainDigit R (T + 3)› +ₚ (stepAux R (T + 3) 7 *ₚ ‹4›)
  setO : (stepRegsAt R (T + 7)).rem =
    (stepRegsAt R (T + 3)).rem.set (wotsPackSlot (2 * pair + 1)) (stepAux R (T + 3) 7)
  zero : (pair + 1 == 64) = true → ∀ s < 5, (stepRegsAt R (T + 7)).rem.get s = Goldilocks.zero
  main : (stepRegsAt R (T + 7)).main =
    poseidon2Perm12
      ⟨lane4Add (stepRegsAt R T).main.b0 (stepChainEndpoint pub R layer tree kpN (2 * pair) T),
       lane4Add (stepRegsAt R T).main.b1
         (stepChainEndpoint pub R layer tree kpN (2 * pair + 1) (T + 3)),
       (stepRegsAt R T).main.b2⟩
  curRoot : (stepRegsAt R (T + 7)).curRoot = (stepRegsAt R T).curRoot
  kp : (stepRegsAt R (T + 7)).kp = (stepRegsAt R T).kp
  treeLo : (stepRegsAt R (T + 7)).treeLo = (stepRegsAt R T).treeLo
  treeHi : (stepRegsAt R (T + 7)).treeHi = (stepRegsAt R T).treeHi

theorem stepPair_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer pair T kpN tree : Nat}
    (hRun : StepRunAt pub R (stepPairOps layer pair) T)
    (hAddr : StepAddrOk (stepRegsAt R T) kpN tree)
    (hl : layer < 64) (hk : kpN < 2 ^ 28) (hp : pair < 64) :
    StepPairFacts pub R layer kpN tree pair T := by
  have h0 : StepRowSem pub R (.wotsChainStep0 layer (2 * pair) (wotsPackSlot (2 * pair))) T :=
    hRun 0 (Nat.le_of_ble_eq_true rfl)
  have h1 : StepRowSem pub R (.wotsChainStep1 layer (2 * pair)) (T + 1) :=
    hRun 1 (Nat.le_of_ble_eq_true rfl)
  have h2 : StepRowSem pub R (.wotsChainStep2 layer (2 * pair) false) (T + 2) :=
    hRun 2 (Nat.le_of_ble_eq_true rfl)
  have h3 : StepRowSem pub R
      (.wotsChainStep0 layer (2 * pair + 1) (wotsPackSlot (2 * pair + 1))) (T + 3) :=
    hRun 3 (Nat.le_of_ble_eq_true rfl)
  have h4 : StepRowSem pub R (.wotsChainStep1 layer (2 * pair + 1)) (T + 3 + 1) :=
    hRun 4 (Nat.le_of_ble_eq_true rfl)
  have h5 : StepRowSem pub R (.wotsChainStep2 layer (2 * pair + 1) true) (T + 3 + 2) :=
    hRun 5 (Nat.le_of_ble_eq_true rfl)
  have h6 : StepRowSem pub R (.wotsTellPairAbsorb pair) (T + 6) :=
    hRun 6 (Nat.le_of_ble_eq_true rfl)
  have hsE : wotsPackSlot (2 * pair) < 6 := Nat.lt_succ_of_lt (wotsPackSlot_lt_5 _)
  have hsO : wotsPackSlot (2 * pair + 1) < 6 := Nat.lt_succ_of_lt (wotsPackSlot_lt_5 _)
  obtain ⟨hdE, hgE, WE, AE, UE, hR3⟩ :=
    stepChain_sem (odd := false) h0 h1 h2 hsE hAddr hl hk (by omega)
  have hA3 : StepAddrOk (stepRegsAt R (T + 3)) kpN tree := by
    rw [hR3]; exact ⟨hAddr.kp, hAddr.lo, hAddr.hi⟩
  obtain ⟨hdO, hgO, WO, AO, UO, hR6⟩ :=
    stepChain_sem (odd := true) h3 h4 h5 hsO hA3 hl hk (by omega)
  have hR6' : stepRegsAt R (T + 6) = _ := hR6
  obtain ⟨hZero, hIn, hR7⟩ := stepSem_wotsTellPairAbsorb h6
  have hR7' : stepRegsAt R (T + 7) = _ := hR7
  refine
    { dE := hdE, dO := hdO, getE := hgE, setE := by rw [hR3], getO := hgO
      setO := by rw [hR7', hR6'], zero := ?_, main := ?_, curRoot := by rw [hR7', hR6', hR3]
      kp := by rw [hR7', hR6', hR3], treeLo := by rw [hR7', hR6', hR3]
      treeHi := by rw [hR7', hR6', hR3] }
  · intro hc s hs
    rw [hR7']
    exact hZero hc s hs
  · rw [hR7']
    show stepPermAt R (T + 6) = _
    unfold stepPermAt stepChainEndpoint
    rw [hIn, hR6', hR3]
    rfl

/-! ### §3.8. `ST_REM_PACK` bookkeeping: the chain rows unpack exactly the packed digits -/

/-- A run of rows owning one `ST_REM_PACK` limb unpacks that limb digit by digit in base `B`;
    since the limb ends at zero and `B ^ len < p`, the limb value is the base-`B` number of
    the digits. -/
theorem stepRemSlot_digits (g : Nat → StepRem) (B : Nat) (hB : 0 < B) (dig : Nat → Nat)
    (x : Nat → Goldilocks) (slotOf : Nat → Nat) (N : Nat)
    (hd : ∀ c < N, dig c < B)
    (hget : ∀ c < N, (g c).get (slotOf c) = ‹dig c› +ₚ (x c *ₚ ‹B›))
    (hset : ∀ c < N, g (c + 1) = (g c).set (slotOf c) (x c))
    (hslot : ∀ c < N, slotOf c < 6)
    (s a len : Nat)
    (hRange : ∀ c < N, slotOf c = s ↔ a ≤ c ∧ c < a + len)
    (haN : a + len ≤ N) (hEnd : (g N).get s = Goldilocks.zero)
    (hLen : B ^ len < goldilocksPrime) :
    ((g 0).get s).val = evalBaseDigits B ((List.range' a len).map dig) := by
  have hStep : ∀ c < N, slotOf c ≠ s → (g (c + 1)).get s = (g c).get s := by
    intro c hc hne
    rw [hset c hc, StepRem.get_set _ _ _ _ (hslot c hc),
      ite_eq_right_of_eq_false _ _ (eq_false (fun h => hne h.symm))]
  have hStepS : ∀ c < N, slotOf c = s → (g (c + 1)).get s = x c := by
    intro c hc he
    rw [hset c hc, StepRem.get_set _ _ _ _ (hslot c hc),
      ite_eq_left_of_eq_true _ _ (eq_true he.symm)]
  have hCarry1 : ∀ c, c ≤ a → (g c).get s = (g 0).get s := by
    intro c
    induction c with
    | zero => intro _; rfl
    | succ c ih =>
      intro hc
      have hcN : c < N := by omega
      rw [hStep c hcN (fun h => by have := (hRange c hcN).mp h; omega)]
      exact ih (by omega)
  have hCarry2 : ∀ k, a + len + k ≤ N → (g (a + len + k)).get s = (g (a + len)).get s := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hcN : a + len + k < N := by omega
      have e : a + len + (k + 1) = a + len + k + 1 := by omega
      rw [e, hStep _ hcN (fun h => by have := (hRange _ hcN).mp h; omega)]
      exact ih (by omega)
  have hChain : ∀ n b, a ≤ b → b + n ≤ a + len →
      UnpackChain B ((g b).get s) ((List.range' b n).map dig) ((g (b + n)).get s) := by
    intro n
    induction n with
    | zero => intro b _ _; exact rfl
    | succ n ih =>
      intro b hab hbn
      have hbN : b < N := by omega
      have hsb : slotOf b = s := (hRange b hbN).mpr ⟨hab, by omega⟩
      refine ⟨hd b hbN, (g (b + 1)).get s, ?_, ?_⟩
      · have h1 := hget b hbN
        rw [hsb] at h1
        rw [h1, hStepS b hbN hsb]
      · have e : b + (n + 1) = b + 1 + n := by omega
        rw [e]
        exact ih (b + 1) (by omega) (by omega)
  have hC := hChain len a (Nat.le_refl a) (Nat.le_refl _)
  have hZ : (g (a + len)).get s = Goldilocks.zero := by
    have h2 := hCarry2 (N - (a + len)) (by omega)
    have e : a + len + (N - (a + len)) = N := by omega
    rw [e, hEnd] at h2
    exact h2.symm
  rw [hZ, hCarry1 a (Nat.le_refl a)] at hC
  have hLen' : B ^ ((List.range' a len).map dig).length < goldilocksPrime := by
    rw [List.length_map, List.length_range']
    exact hLen
  exact (baseBUnpackChain_backward B hB _ _ hLen' hC).1

/-- Absorbing an even-length list of digests followed by one more pair applies the two-block
    permutation step once more. -/
theorem absorbPairsPoly_append_pair {Dg S : Type} (perm1 : S → Dg → S)
    (perm2 : S → Dg → Dg → S) (e0 e1 : Dg) :
    ∀ (xs : List Dg) (st : S), xs.length % 2 = 0 →
      absorbPairsPoly perm1 perm2 (xs ++ [e0, e1]) st none =
        perm2 (absorbPairsPoly perm1 perm2 xs st none) e0 e1
  | [], _, _ => by simp only [List.nil_append, absorbPairsPoly.public_eqs]
  | [_], _, h => by simp at h
  | x :: y :: rest, st, h => by
    have hr : rest.length % 2 = 0 := by
      simp only [List.length_cons] at h
      omega
    simpa only [List.cons_append, absorbPairsPoly.public_eqs] using
      absorbPairsPoly_append_pair perm1 perm2 e0 e1 rest (perm2 st x y) hr

/-! ### §3.9. The WOTS+C part of one layer -/

/-- Row of the `WotsChainStep0` of chain `c` in a layer whose `WotsTellInit` row is `t0`. -/
@[expose] def stepChainRow (t0 c : Nat) : Nat := t0 + 1 + 7 * (c / 2) + 3 * (c % 2)

/-- The WOTS+C part of a layer: `WotsTellInit`, 64 chain pairs, `WotsTellFinalSqueeze`. -/
@[expose] def stepWotsOps (layer : Nat) : List StepOp :=
  [StepOp.wotsTellInit layer] ++ (List.range 64).flatMap (stepPairOps layer) ++
    [StepOp.wotsTellFinalSqueeze]

/-- The 128 chain endpoints recovered by the rows of a layer starting at row `t0`. -/
@[expose] def stepLayerEndpoints (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (layer tree kpN t0 : Nat) : List Lane4 :=
  (List.range 128).map fun c => stepChainEndpoint pub R layer tree kpN c (stepChainRow t0 c)

/-- **WOTS+C layer rows.** The 450 rows `WotsTellInit .. WotsTellFinalSqueeze` of a layer
    leave in `ST_WORK` the `T_ell` sponge of the 128 walked chain endpoints, and every
    `ST_REM_PACK` limb entering the layer is the base-4 number of the remaining-step counts
    `3 - d_c` of the chains it owns. -/
theorem stepWots_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer t0 kpN tree : Nat}
    (hRun : StepRunAt pub R (stepWotsOps layer) t0)
    (hAddr : StepAddrOk (stepRegsAt R t0) kpN tree) (hl : layer < 64) (hk : kpN < 2 ^ 28) :
    (∀ c < 128, stepChainDigit R (stepChainRow t0 c) ≤ 3) ∧
    (∀ s a len : Nat, (∀ c < 128, wotsPackSlot c = s ↔ a ≤ c ∧ c < a + len) → s < 5 →
      a + len ≤ 128 → 4 ^ len < goldilocksPrime →
      ((stepRegsAt R t0).rem.get s).val =
        evalBaseDigits 4 ((List.range' a len).map
          (fun c => 3 - stepChainDigit R (stepChainRow t0 c)))) ∧
    (stepRegsAt R (t0 + 450)).work =
      compressWotsEndpointsSponge pub.1.pkSeed layer tree kpN
        (stepLayerEndpoints pub R layer tree kpN t0) ∧
    (stepRegsAt R (t0 + 450)).curRoot = (stepRegsAt R t0).curRoot ∧
    StepAddrOk (stepRegsAt R (t0 + 450)) kpN tree ∧
    (stepRegsAt R (t0 + 450)).cursor = ‹kpN› := by
  have hInit : StepRowSem pub R (.wotsTellInit layer) t0 := hRun.append_left.append_left.head
  have hPairs : StepRunAt pub R ((List.range 64).flatMap (stepPairOps layer)) (t0 + 1) :=
    hRun.append_left.append_right
  have hPair : ∀ p < 64, StepRunAt pub R (stepPairOps layer p) (t0 + 1 + p * 7) :=
    StepRunAt.flatMap_range (L := 7) (fun _ => rfl) 64 hPairs
  have hlen : ([StepOp.wotsTellInit layer] ++
      (List.range 64).flatMap (stepPairOps layer)).length = 449 := by
    rw [List.length_append, flatMap_range_uniform_length _ 7 (fun _ => rfl)]
    rfl
  have hSq : StepRowSem pub R .wotsTellFinalSqueeze (t0 + 449) := by
    have h := hRun.append_right
    rw [hlen] at h
    exact h.head
  obtain ⟨hInInit, hR1⟩ := stepSem_wotsTellInit hInit
  have hFrame : ∀ p, p ≤ 64 →
      (stepRegsAt R (t0 + 1 + p * 7)).kp = (stepRegsAt R t0).kp ∧
      (stepRegsAt R (t0 + 1 + p * 7)).treeLo = (stepRegsAt R t0).treeLo ∧
      (stepRegsAt R (t0 + 1 + p * 7)).treeHi = (stepRegsAt R t0).treeHi ∧
      (stepRegsAt R (t0 + 1 + p * 7)).curRoot = (stepRegsAt R t0).curRoot := by
    intro p
    induction p with
    | zero =>
      intro _
      have h0 : stepRegsAt R (t0 + 1 + 0 * 7) = _ := hR1
      rw [h0]
      exact ⟨rfl, rfl, rfl, rfl⟩
    | succ p ih =>
      intro hp
      obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
      have hA : StepAddrOk (stepRegsAt R (t0 + 1 + p * 7)) kpN tree :=
        ⟨i1.trans hAddr.kp, i2.trans hAddr.lo, i3.trans hAddr.hi⟩
      have F := stepPair_sem (hPair p (by omega)) hA hl hk (by omega)
      have e : t0 + 1 + (p + 1) * 7 = t0 + 1 + p * 7 + 7 := by omega
      rw [e]
      exact ⟨F.kp.trans i1, F.treeLo.trans i2, F.treeHi.trans i3, F.curRoot.trans i4⟩
  have hF : ∀ p, p < 64 → StepPairFacts pub R layer kpN tree p (t0 + 1 + p * 7) := by
    intro p hp
    obtain ⟨i1, i2, i3, _⟩ := hFrame p (by omega)
    exact stepPair_sem (hPair p hp)
      ⟨i1.trans hAddr.kp, i2.trans hAddr.lo, i3.trans hAddr.hi⟩ hl hk hp
  have rowE : ∀ p, stepChainRow t0 (2 * p) = t0 + 1 + p * 7 := by
    intro p; unfold stepChainRow; omega
  have rowO : ∀ p, stepChainRow t0 (2 * p + 1) = t0 + 1 + p * 7 + 3 := by
    intro p; unfold stepChainRow; omega
  have rowN : ∀ p, stepChainRow t0 (2 * p + 1 + 1) = t0 + 1 + p * 7 + 7 := by
    intro p; unfold stepChainRow; omega
  have hSplit : ∀ c, c < 128 → ∃ p, p < 64 ∧ (c = 2 * p ∨ c = 2 * p + 1) :=
    fun c hc => ⟨c / 2, by omega, by omega⟩
  have hd : ∀ c < 128, stepChainDigit R (stepChainRow t0 c) ≤ 3 := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE]; exact (hF p hp).dE
    · rw [rowO]; exact (hF p hp).dO
  have hget : ∀ c < 128, ((stepRegsAt R (stepChainRow t0 c)).rem).get (wotsPackSlot c) =
      ‹3 - stepChainDigit R (stepChainRow t0 c)› +ₚ (stepAux R (stepChainRow t0 c) 7 *ₚ ‹4›) := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE]; exact (hF p hp).getE
    · rw [rowO]; exact (hF p hp).getO
  have hset : ∀ c < 128, (stepRegsAt R (stepChainRow t0 (c + 1))).rem =
      ((stepRegsAt R (stepChainRow t0 c)).rem).set (wotsPackSlot c)
        (stepAux R (stepChainRow t0 c) 7) := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE, rowO]; exact (hF p hp).setE
    · rw [rowO, rowN]; exact (hF p hp).setO
  have hEnd : ∀ s < 5, ((stepRegsAt R (stepChainRow t0 128)).rem).get s = Goldilocks.zero := by
    intro s hs
    have e : stepChainRow t0 128 = t0 + 1 + 63 * 7 + 7 := by unfold stepChainRow; omega
    rw [e]
    exact (hF 63 (by decide)).zero rfl s hs
  have hG0 : (stepRegsAt R (stepChainRow t0 0)).rem = (stepRegsAt R t0).rem := by
    have e : stepChainRow t0 0 = t0 + 1 := by unfold stepChainRow; omega
    rw [e, hR1]
  have hMain : ∀ p, p ≤ 64 → (stepRegsAt R (t0 + 1 + p * 7)).main =
      absorbDigest4Pairs (stepPermAt R t0)
        ((List.range (2 * p)).map fun c =>
          stepChainEndpoint pub R layer tree kpN c (stepChainRow t0 c)) := by
    intro p
    induction p with
    | zero =>
      intro _
      have h0 : stepRegsAt R (t0 + 1 + 0 * 7) = _ := hR1
      rw [h0]
      simp only [Nat.mul_zero, List.range_zero, List.map_nil,
        absorbDigest4Pairs.public_eqs, absorbPairsPoly.public_eqs]
    | succ p ih =>
      intro hp
      have F := hF p (by omega)
      have e : t0 + 1 + (p + 1) * 7 = t0 + 1 + p * 7 + 7 := by omega
      have e2 : 2 * (p + 1) = 2 * p + 1 + 1 := by omega
      rw [e, F.main, ih (by omega), e2, List.range_succ, List.range_succ, List.append_assoc,
        List.map_append]
      simp only [absorbDigest4Pairs.public_eqs]
      have hEven : ((List.range (2 * p)).map fun c =>
          stepChainEndpoint pub R layer tree kpN c (stepChainRow t0 c)).length % 2 = 0 := by
        rw [List.length_map, List.length_range]
        omega
      have hApp := absorbPairsPoly_append_pair
        (fun (s : Poseidon2State12) (e0 : Lane4) =>
          poseidon2Perm12 ⟨lane4Add s.b0 e0, s.b1, s.b2⟩)
        (fun (s : Poseidon2State12) (e0 e1 : Lane4) =>
          poseidon2Perm12 ⟨lane4Add s.b0 e0, lane4Add s.b1 e1, s.b2⟩)
        (stepChainEndpoint pub R layer tree kpN (2 * p) (stepChainRow t0 (2 * p)))
        (stepChainEndpoint pub R layer tree kpN (2 * p + 1) (stepChainRow t0 (2 * p + 1)))
        _ (stepPermAt R t0) hEven
      rw [rowE, rowO] at hApp
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
      rw [rowE, rowO]
      exact hApp.symm
  obtain ⟨hInSq, hR450⟩ := stepSem_wotsTellFinalSqueeze hSq
  have hR450' : stepRegsAt R (t0 + 450) = _ := hR450
  obtain ⟨f1, f2, f3, f4⟩ := hFrame 64 (Nat.le_refl _)
  have e64 : t0 + 1 + 64 * 7 = t0 + 449 := by omega
  rw [e64] at f1 f2 f3 f4
  have hM64 := hMain 64 (Nat.le_refl _)
  rw [e64] at hM64
  refine ⟨hd, ?_, ?_, ?_, ?_, ?_⟩
  · intro s a len hRange hs haN hLen
    have h := stepRemSlot_digits
      (fun c => (stepRegsAt R (stepChainRow t0 c)).rem) 4 (by decide)
      (fun c => 3 - stepChainDigit R (stepChainRow t0 c))
      (fun c => stepAux R (stepChainRow t0 c) 7) wotsPackSlot 128
      (fun c hc => by have := hd c hc; show 3 - _ < 4; omega) hget hset
      (fun c _ => Nat.lt_succ_of_lt (wotsPackSlot_lt_5 c)) s a len hRange haN (hEnd s hs) hLen
    rw [← hG0]
    exact h
  · have hInit' : (R t0).stIn =
        ⟨pub.1.pkSeed,
         ⟨‹(layer % 2 ^ 32) * 2 ^ 32 + kpN % 2 ^ 32›, ‹tree % 2 ^ 32›,
          ‹(tree / 2 ^ 32) % 2 ^ 32›, ‹128›⟩,
         ⟨domainWotsPk, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩ := by
      rw [hInInit, hAddr.kp, hAddr.lo, hAddr.hi, ← g_ofNat_add,
        Nat.mod_eq_of_lt (by omega : layer < 2 ^ 32), Nat.mod_eq_of_lt (by omega : kpN < 2 ^ 32)]
    rw [hR450']
    show (stepPermAt R (t0 + 449)).b0 = _
    unfold stepPermAt
    rw [hInSq]
    unfold stepSqueezeIn
    rw [hM64]
    simp only [stepPermAt, compressWotsEndpointsSponge.public_eqs, stepLayerEndpoints]
    rw [hInit', List.length_map, List.length_range]
  · rw [hR450']; exact f4
  · rw [hR450']
    exact ⟨f1.trans hAddr.kp, f2.trans hAddr.lo, f3.trans hAddr.hi⟩
  · rw [hR450']
    exact f1.trans hAddr.kp

/-! ### §3.10. The subtree Merkle path of one layer -/

/-- The Merkle part of a layer: per level one `XmssMerkleBlockA` and one `XmssMerkleBlockB`. -/
@[expose] def stepMerkleOps (layer subHeight : Nat) (isTopFinal : Bool) : List StepOp :=
  (List.range subHeight).flatMap (fun lvl =>
    [StepOp.xmssMerkleBlockA layer lvl,
     StepOp.xmssMerkleBlockB (lvl + 1 == subHeight) ((lvl + 1 == subHeight) && isTopFinal)])

theorem pushLayerWotsAndMerkle_eq (layer subHeight : Nat) (isTopFinal : Bool) :
    pushLayerWotsAndMerkle layer subHeight isTopFinal =
      stepWotsOps layer ++ stepMerkleOps layer subHeight isTopFinal := by
  simp only [pushLayerWotsAndMerkle.public_eqs, stepWotsOps, stepMerkleOps]
  rfl

/-- The 2-block node sponge with its address limbs given as field elements. -/
def stepNodeHashF (domainTag meta0 treeLo treeHi : Goldilocks) (pkSeed left right : Lane4) :
    Lane4 :=
  (poseidon2Perm12
    ⟨lane4Add (poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b0 right,
     ⟨(poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b1.x0 +ₚ Goldilocks.one,
      (poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b1.x1 +ₚ poseidon2IvTag,
      (poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b1.x2,
      (poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b1.x3⟩,
     (poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b2⟩).b0
#export_eqns stepNodeHashF

/-- Agreement of two register files outside `ST_SUB_SPONGE`, `ST_WORK`, `ST_CURSOR_IDX` and
    the two chain-step flags. -/
structure StepFrameSWC (a b : StepRegs) : Prop where
  curRoot : a.curRoot = b.curRoot
  kp : a.kp = b.kp
  treeLo : a.treeLo = b.treeLo
  treeHi : a.treeHi = b.treeHi
  rem : a.rem = b.rem
  main : a.main = b.main

/-- A Merkle `BlockA` row with domain tag `tag` and node address limb `pre + aux[1]`. -/
structure StepMerkleARow (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow) (t : Nat)
    (tag pre : Goldilocks) : Prop where
  bit : stepAux R t 0 = Goldilocks.zero ∨ stepAux R t 0 = Goldilocks.one
  cur : (stepRegsAt R t).cursor = (stepAux R t 0 +ₚ stepAux R t 1) +ₚ stepAux R t 1
  stIn : (R t).stIn =
    ⟨pub.1.pkSeed, lane4MuxL (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2),
     ⟨tag, pre +ₚ stepAux R t 1, (stepRegsAt R t).treeLo, (stepRegsAt R t).treeHi⟩⟩
  next : stepRegsAt R (t + 1) =
    { stepRegsAt R t with
      sub := stepPermAt R t
      work := lane4Mux (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2)
      cursor := stepAux R t 1 }

theorem stepMerkleARow_xmss {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer lvl t : Nat} (h : StepRowSem pub R (.xmssMerkleBlockA layer lvl) t) :
    StepMerkleARow pub R t domainMerkleNode ‹layer * 2 ^ 48 + (lvl + 1) * 2 ^ 32› :=
  match stepSem_xmssMerkleBlockA h with
  | ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩

/-- One Merkle level: the `BlockA` row followed by a row whose `st_in` is the second block
    computes the 2-block node sponge of the selected `(left, right)` pair. -/
theorem stepMerkleLevel_hash {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {tag pre : Goldilocks} {t : Nat} (hA : StepMerkleARow pub R t tag pre)
    (hInB : (R (t + 1)).stIn = stepMerkleBIn (stepRegsAt R (t + 1))) :
    (stepPermAt R (t + 1)).b0 =
      stepNodeHashF tag (pre +ₚ stepAux R t 1)
        (stepRegsAt R t).treeLo (stepRegsAt R t).treeHi pub.1.pkSeed
        (lane4MuxL (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2))
        (lane4Mux (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2)) := by
  unfold stepPermAt
  rw [hInB]
  unfold stepMerkleBIn
  rw [hA.next]
  show (poseidon2Perm12 _).b0 = _
  unfold stepPermAt stepNodeHashF
  rw [hA.stIn]

/-- A halving chain `X l = bit l + 2 * X (l + 1)` ending at zero determines every `X l` and
    every bit from `X 0`. -/
private theorem stepHalving_chain (X : Nat → Goldilocks) (bit : Nat → Nat) (h : Nat)
    (hStep : ∀ l < h, bit l < 2 ∧ X l = ‹bit l› +ₚ (X (l + 1) *ₚ ‹2›))
    (hEnd : X h = Goldilocks.zero) (hPow : 2 ^ h < goldilocksPrime) :
    (X 0).val < 2 ^ h ∧
    ∀ l, l ≤ h → (X l).val = (X 0).val / 2 ^ l ∧ (l < h → bit l = ((X 0).val / 2 ^ l) % 2) := by
  have hChain : ∀ n l, l + n = h →
      UnpackChain 2 (X l) ((List.range' l n).map bit) Goldilocks.zero := by
    intro n
    induction n with
    | zero =>
      intro l hl
      have e : l = h := by omega
      rw [e]
      exact hEnd
    | succ n ih =>
      intro l hl
      have hs := hStep l (by omega)
      exact ⟨hs.1, X (l + 1), hs.2, ih (l + 1) (by omega)⟩
  have hVal : ∀ l, l ≤ h →
      (X l).val = evalBaseDigits 2 ((List.range' l (h - l)).map bit) ∧ (X l).val < 2 ^ (h - l) := by
    intro l hl
    have hLen : 2 ^ ((List.range' l (h - l)).map bit).length < goldilocksPrime := by
      rw [List.length_map, List.length_range']
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (Nat.sub_le h l)) hPow
    have hB := baseBUnpackChain_backward 2 (by decide) _ (X l) hLen (hChain (h - l) l (by omega))
    refine ⟨hB.1, ?_⟩
    have h2 := hB.2.1
    rw [List.length_map, List.length_range'] at h2
    exact h2
  have hRel : ∀ l, l < h → (X l).val = bit l + 2 * (X (l + 1)).val := by
    intro l hl
    have e : h - l = (h - (l + 1)) + 1 := by omega
    have h1 := (hVal l (by omega)).1
    rw [e] at h1
    rw [h1, (hVal (l + 1) (by omega)).1]
    rfl
  have hDiv : ∀ l, l ≤ h → (X l).val = (X 0).val / 2 ^ l := by
    intro l
    induction l with
    | zero => intro _; rw [Nat.pow_zero, Nat.div_one]
    | succ l ih =>
      intro hl
      have hr := hRel l (by omega)
      have hb := (hStep l (by omega)).1
      have ih' := ih (by omega)
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← ih']
      omega
  refine ⟨?_, fun l hl => ⟨hDiv l hl, fun hlt => ?_⟩⟩
  · have h0 := (hVal 0 (Nat.zero_le _)).2
    rw [Nat.sub_zero] at h0
    exact h0
  · have hr := hRel l hlt
    have hb := (hStep l hlt).1
    rw [← hDiv l hl]
    omega

/-- Folding per-level parents along an authentication path is `merkleWalkRoot`. -/
private theorem stepMerkleWalk_eq (domainTag : Goldilocks) (pkSeed : Lane4) (layer tree : Nat)
    (addr : Nat → Nat → Nat) (sib : Nat → Lane4) (W : Nat → Lane4) (idx0 h : Nat)
    (hStep : ∀ l < h, W (l + 1) =
      if (idx0 / 2 ^ l) % 2 == 0 then
        merkleAddrNodeHash domainTag pkSeed layer tree addr (1 + l) (idx0 / 2 ^ (l + 1)) (W l) (sib l)
      else
        merkleAddrNodeHash domainTag pkSeed layer tree addr (1 + l) (idx0 / 2 ^ (l + 1)) (sib l) (W l)) :
    merkleWalkRoot domainTag pkSeed layer tree addr 1 idx0 (W 0) ((List.range h).map sib) = W h := by
  have hGen : ∀ n l, l + n = h →
      merkleWalkRoot domainTag pkSeed layer tree addr (1 + l) (idx0 / 2 ^ l) (W l)
        ((List.range' l n).map sib) = W h := by
    intro n
    induction n with
    | zero =>
      intro l hl
      have e : l = h := by omega
      rw [e]
      simp only [List.range'_zero, List.map_nil, merkleWalkRoot.public_eqs,
        merkleWalkPoly.public_eqs]
    | succ n ih =>
      intro l hl
      have hs := hStep l (by omega)
      have hIdx : idx0 / 2 ^ l / 2 = idx0 / 2 ^ (l + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      have hI := ih (l + 1) (by omega)
      rw [hs, ← hIdx] at hI
      simpa only [List.range'_succ, List.map_cons, merkleWalkRoot.public_eqs,
        merkleWalkPoly.public_eqs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hI
  have h0 := hGen h 0 (by omega)
  rw [Nat.pow_zero, Nat.div_one, ← List.range_eq_range'] at h0
  exact h0

theorem stepNodeHashF_xmss (pkSeed : Lane4) (layer tree l parent : Nat) (left right : Lane4)
    (hl : layer < 65536) (hlv : 1 + l < 65536) (hp : parent < 2 ^ 32) :
    stepNodeHashF domainMerkleNode (‹layer * 2 ^ 48 + (l + 1) * 2 ^ 32› +ₚ ‹parent›)
        ‹tree % 2 ^ 32› ‹(tree / 2 ^ 32) % 2 ^ 32› pkSeed left right =
      merkleAddrNodeHash domainMerkleNode pkSeed layer tree xmssNodeAddr (1 + l) parent left right := by
  simp only [merkleAddrNodeHash.public_eqs, merkleNodeHash.public_eqs, xmssNodeAddr.public_eqs, stepNodeHashF]
  rw [← g_ofNat_add, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hlv, Nat.mod_eq_of_lt hp,
    Nat.add_comm 1 l]

/-- **Merkle rows.** The `2 * h` rows of an authentication path walk `merkleWalkRoot` from the
    node in `ST_WORK` at leaf index `idx0`; the cursor halving forces `idx0 < 2 ^ h`. The node
    address limbs are abstract: `hNode` relates the row's address limb to the addressing
    `addr` of the walked tree. -/
theorem stepMerkle_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {tag : Goldilocks} {M : Nat → Goldilocks} {layerV treeV : Nat} {addr : Nat → Nat → Nat}
    {h t1 idx0 : Nat}
    (hA : ∀ l < h, StepMerkleARow pub R (t1 + 2 * l) tag (M l))
    (hBin : ∀ l < h, (R (t1 + 2 * l + 1)).stIn = stepMerkleBIn (stepRegsAt R (t1 + 2 * l + 1)))
    (hBnext : ∀ l, l + 1 < h → stepRegsAt R (t1 + 2 * l + 2) =
      { stepRegsAt R (t1 + 2 * l + 1) with work := (stepPermAt R (t1 + 2 * l + 1)).b0 })
    (hLastCur : (stepRegsAt R (t1 + 2 * (h - 1) + 1)).cursor = Goldilocks.zero)
    (hCur : (stepRegsAt R t1).cursor = ‹idx0›)
    (hIdx : idx0 < 2 ^ 28) (hh : 0 < h) (hh28 : h ≤ 28)
    (hNode : ∀ l < h, StepFrameSWC (stepRegsAt R (t1 + 2 * l)) (stepRegsAt R t1) →
      ∀ (L Rr : Lane4),
      stepNodeHashF tag (M l +ₚ ‹idx0 / 2 ^ (l + 1)›) (stepRegsAt R t1).treeLo
          (stepRegsAt R t1).treeHi pub.1.pkSeed L Rr =
        merkleAddrNodeHash tag pub.1.pkSeed layerV treeV addr (1 + l) (idx0 / 2 ^ (l + 1)) L Rr) :
    idx0 < 2 ^ h ∧
    merkleWalkRoot tag pub.1.pkSeed layerV treeV addr 1 idx0
        (stepRegsAt R t1).work ((List.range h).map (fun l => stepAuxLane R (t1 + 2 * l) 2)) =
      (stepPermAt R (t1 + 2 * (h - 1) + 1)).b0 ∧
    StepFrameSWC (stepRegsAt R (t1 + 2 * (h - 1) + 1)) (stepRegsAt R t1) := by
  let X : Nat → Goldilocks := fun l => match l with
    | 0 => ‹idx0›
    | l + 1 => stepAux R (t1 + 2 * l) 1
  let W : Nat → Lane4 := fun l => match l with
    | 0 => (stepRegsAt R t1).work
    | l + 1 => (stepPermAt R (t1 + 2 * l + 1)).b0
  have hA1 : ∀ l, l < h →
      (stepRegsAt R (t1 + 2 * l + 1)).cursor = stepAux R (t1 + 2 * l) 1 ∧
      StepFrameSWC (stepRegsAt R (t1 + 2 * l + 1)) (stepRegsAt R (t1 + 2 * l)) := by
    intro l hl'
    rw [(hA l hl').next]
    exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hInv : ∀ l, l < h →
      (stepRegsAt R (t1 + 2 * l)).cursor = X l ∧
      (stepRegsAt R (t1 + 2 * l)).work = W l ∧
      StepFrameSWC (stepRegsAt R (t1 + 2 * l)) (stepRegsAt R t1) := by
    intro l
    induction l with
    | zero => intro _; exact ⟨hCur, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    | succ l ih =>
      intro hl'
      obtain ⟨_, _, iF⟩ := ih (by omega)
      obtain ⟨c1, f1⟩ := hA1 l (by omega)
      have hN := hBnext l hl'
      have e : t1 + 2 * (l + 1) = t1 + 2 * l + 2 := by omega
      rw [e, hN]
      exact ⟨c1, rfl, ⟨f1.curRoot.trans iF.curRoot, f1.kp.trans iF.kp,
        f1.treeLo.trans iF.treeLo, f1.treeHi.trans iF.treeHi, f1.rem.trans iF.rem,
        f1.main.trans iF.main⟩⟩
  have hStepX : ∀ l < h, (stepAux R (t1 + 2 * l) 0).val < 2 ∧
      X l = ‹(stepAux R (t1 + 2 * l) 0).val› +ₚ (X (l + 1) *ₚ ‹2›) := by
    intro l hl'
    have hb := (hA l hl').bit
    have hc := (hA l hl').cur
    obtain ⟨iC, _, _⟩ := hInv l hl'
    refine ⟨by rcases hb with hb | hb <;> rw [hb] <;> decide, ?_⟩
    rw [← iC, hc, g_ofNat_self]
    show _ = stepAux R (t1 + 2 * l) 0 +ₚ (stepAux R (t1 + 2 * l) 1 *ₚ ‹2›)
    have h2 : (‹2› : Goldilocks) = Goldilocks.one +ₚ Goldilocks.one := by decide +kernel
    rw [h2, g_left_distrib, g_mul_one, g_add_assoc]
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have hEndX : X (h' + 1) = Goldilocks.zero := by
    obtain ⟨c1, _⟩ := hA1 h' (by omega)
    show stepAux R (t1 + 2 * h') 1 = Goldilocks.zero
    rw [← c1]
    exact hLastCur
  have hPow : 2 ^ (h' + 1) < goldilocksPrime :=
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hh28) (by decide)
  have hip : idx0 < goldilocksPrime := Nat.lt_trans hIdx (by decide)
  have hX0 : (X 0).val = idx0 := Nat.mod_eq_of_lt hip
  obtain ⟨hLt, hBits⟩ := stepHalving_chain X (fun l => (stepAux R (t1 + 2 * l) 0).val) (h' + 1)
    hStepX hEndX hPow
  rw [hX0] at hLt hBits
  have hXval : ∀ l, l ≤ h' + 1 → X l = ‹idx0 / 2 ^ l› := by
    intro l hl'
    rw [← (hBits l hl').1, g_ofNat_self]
  have hStepW : ∀ l < h' + 1, W (l + 1) =
      if (idx0 / 2 ^ l) % 2 == 0 then
        merkleAddrNodeHash tag pub.1.pkSeed layerV treeV addr (1 + l)
          (idx0 / 2 ^ (l + 1)) (W l) (stepAuxLane R (t1 + 2 * l) 2)
      else
        merkleAddrNodeHash tag pub.1.pkSeed layerV treeV addr (1 + l)
          (idx0 / 2 ^ (l + 1)) (stepAuxLane R (t1 + 2 * l) 2) (W l) := by
    intro l hl'
    have hb := (hA l hl').bit
    have hH := stepMerkleLevel_hash (hA l hl') (hBin l hl')
    obtain ⟨_, iW, iF⟩ := hInv l hl'
    have hY : stepAux R (t1 + 2 * l) 1 = ‹idx0 / 2 ^ (l + 1)› := hXval (l + 1) (by omega)
    have hBit := (hBits l (by omega)).2 hl'
    show (stepPermAt R (t1 + 2 * l + 1)).b0 = _
    rw [hH, hY, iF.treeLo, iF.treeHi, iW, hNode l hl' iF]
    rcases hb with hb | hb
    · have h0 : (idx0 / 2 ^ l) % 2 = 0 := by rw [← hBit, hb]; rfl
      rw [hb, lane4MuxL_zero, lane4Mux_zero, h0]
      rfl
    · have h1 : (idx0 / 2 ^ l) % 2 = 1 := by rw [← hBit, hb]; rfl
      rw [hb, lane4MuxL_one, lane4Mux_one, h1]
      rfl
  have hWalk := stepMerkleWalk_eq tag pub.1.pkSeed layerV treeV addr
    (fun l => stepAuxLane R (t1 + 2 * l) 2) W idx0 (h' + 1) hStepW
  obtain ⟨_, _, iF⟩ := hInv h' (by omega)
  obtain ⟨_, f1⟩ := hA1 h' (by omega)
  have e : h' + 1 - 1 = h' := by omega
  rw [e]
  exact ⟨hLt, hWalk, ⟨f1.curRoot.trans iF.curRoot, f1.kp.trans iF.kp,
    f1.treeLo.trans iF.treeLo, f1.treeHi.trans iF.treeHi, f1.rem.trans iF.rem,
    f1.main.trans iF.main⟩⟩

end HemStepOp256Machine
end Qsag
end

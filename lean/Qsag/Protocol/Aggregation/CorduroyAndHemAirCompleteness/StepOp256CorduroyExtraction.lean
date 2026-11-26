module
/-
# `CorduroyPoseidon2` Opcode Row Semantics and Signature Extraction

Stateless derive rows (FORS indices and the 64-bit leaf index), the FORS rows with the sponge of
their roots, the hypertree layers of the stateless profile, and the active `CorduroyPoseidon2`
slot: an accepted table yields a native signature (`stepOp256TableOk_corduroy_extract`).
-/

public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.StepOp256XmssExtraction

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

/-! ### §3.14. Row semantics of the `CorduroyPoseidon2` opcodes -/



theorem stepSem_statelessDeriveBlock0 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .statelessDeriveBlock0 t) :
    (R t).stIn =
      ⟨pub.1.pkSeed, pub.1.pkRoot,
       ⟨domainHMsgStateless, pub.2.limb4, Goldilocks.zero, poseidon2IvTag⟩⟩ ∧
    stepRegsAt R (t + 1) =
      { curRoot := lane4Zero
        kp := Goldilocks.zero
        treeLo := Goldilocks.zero
        treeHi := Goldilocks.zero
        rem := stepRemZero
        main := stepPermAt R t
        sub := state12Zero
        work := lane4Zero
        cursor := Goldilocks.zero
        acc := Goldilocks.zero
        u2 := Goldilocks.zero } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 1) (gz% hG 3)
    (gz% hG 5) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gzz% hG 10) (gz% hG 11), (regs% h)⟩

theorem stepSem_statelessDeriveBlock1 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .statelessDeriveBlock1 t) :
    (R t).stIn =
      ⟨lane4Add (stepRegsAt R t).main.b0 (stepAuxLane R t 0),
       lane4Add (stepRegsAt R t).main.b1 ⟨pub.2.limb0, pub.2.limb1, pub.2.limb2, pub.2.limb3⟩,
       (stepRegsAt R t).main.b2⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with main := stepPermAt R t, rem := stepRemZero } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 3) (gz% hG 6) (gz% hG 9) (gz% hG 1) (gz% hG 4)
    (gz% hG 7) (gz% hG 10) (gz% hG 2) (gz% hG 5) (gz% hG 8) (gz% hG 11), (regs% h)⟩

/-- `StatelessDecompLimb l`, `l < 5`: the FORS index bytes of the limb are packed into
    `ST_REM_PACK`; nothing else changes. -/
theorem stepSem_statelessDecompLimb_pack {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {l t : Nat} (hl : l < 5) (h : StepRowSem pub R (.statelessDecompLimb l) t) :
    allZeroGoldilocks (stepLimb63Decomp (stepOpRowInputsPerm pub (R t)) l) = true ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := ⟨stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 7,
          stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 8,
          stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 9,
          stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 10,
          stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 11,
          stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 12⟩ } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  rcases l with _ | _ | _ | _ | _ | l
  · exact ⟨hG, (regs% h)⟩
  · exact ⟨hG, (regs% h)⟩
  · exact ⟨hG, (regs% h)⟩
  · exact ⟨hG, (regs% h)⟩
  · exact ⟨hG, (regs% h)⟩
  · exact absurd hl (by omega)

/-- `StatelessDecompLimb 5`: the low 32 bits of the limb give `kp_idx` (4 bits) and the low
    28 bits of the tree index. -/
theorem stepSem_statelessDecompLimb5 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R (.statelessDecompLimb 5) t) :
    allZeroGoldilocks (stepLimb63Decomp (stepOpRowInputsPerm pub (R t)) 5) = true ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        kp := stepAux R t 0 +ₚ (stepAux R t 1 *ₚ ‹4›)
        treeLo := stepHi28 (stepOpRowInputsPerm pub (R t)) } :=
  ⟨by simpa only [stepOpKindAndC0.public_eqs, stepOpGuardResiduals] using h.guard, (regs% h)⟩

/-- `StatelessDecompLimb 6`: the low 32 bits of the limb give tree-index bits 28..59. -/
theorem stepSem_statelessDecompLimb6 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R (.statelessDecompLimb 6) t) :
    allZeroGoldilocks (stepLimb63Decomp (stepOpRowInputsPerm pub (R t)) 6) = true ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        treeLo := (stepRegsAt R t).treeLo +ₚ
          ((stepAux R t 0 +ₚ (stepAux R t 1 *ₚ ‹4›)) *ₚ ‹2 ^ 28›)
        treeHi := stepHi28 (stepOpRowInputsPerm pub (R t)) } :=
  ⟨by simpa only [stepOpKindAndC0.public_eqs, stepOpGuardResiduals] using h.guard, (regs% h)⟩

theorem stepSem_forsRootsSpongeInit {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .forsRootsSpongeInit t) :
    (R t).stIn =
      ⟨pub.1.pkSeed,
       ⟨(stepRegsAt R t).kp, (stepRegsAt R t).treeLo, (stepRegsAt R t).treeHi, ‹32›⟩,
       ⟨domainForsRoots, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gzz% hG 9) (gzz% hG 10) (gz% hG 11), (regs% h)⟩



set_option maxHeartbeats 800000 in
theorem stepSem_forsLeafHash {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {j slot t : Nat} (hs : slot < 6) (h : StepRowSem pub R (.forsLeafHash j slot) t) :
    (∀ k < 4, (stepAux R t (4 + k)).val < 4) ∧
    (stepRegsAt R t).rem.get slot = stepForsIdxF R t +ₚ (stepAux R t 8 *ₚ ‹256›) ∧
    (R t).stIn =
      ⟨stepAuxLane R t 0, pub.1.pkSeed,
       ⟨domainForsLeaf,
        ((stepRegsAt R t).kp *ₚ ‹2 ^ 24›) +ₚ (‹j * 2 ^ 8› +ₚ stepForsIdxF R t),
        (stepRegsAt R t).treeLo, (stepRegsAt R t).treeHi⟩⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := (stepRegsAt R t).rem.set slot (stepAux R t 8)
        work := stepFfAt R t (stepAuxLane R t 0)
        cursor := stepForsIdxF R t } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  have hQ : allZeroGoldilocks ((List.range 4).map
      (fun k => quarticBase4 (stepAux R t (4 + k)))) = true := allZero_take hG 4
  have hQ' : ∀ k < 4, (stepAux R t (4 + k)).val < 4 := fun k hk =>
    (quarticBase4_eq_zero_iff _).mp ((allZero_map_iff 4 _).mp hQ k hk)
  step_guard_nf hG
  rcases slot with _ | _ | _ | _ | _ | _ | slot
  all_goals first
    | exact ⟨hQ', gz% hG 4,
        state12_ext12 (gz% hG 5) (gz% hG 7) (gz% hG 9) (gz% hG 11) (gz% hG 6) (gz% hG 8)
          (gz% hG 10) (gz% hG 12) (gz% hG 13) (gz% hG 14) (gz% hG 15) (gz% hG 16), (regs% h)⟩
    | exact absurd hs (by omega)

theorem stepMerkleARow_fors {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {j lvl t : Nat} (h : StepRowSem pub R (.forsMerkleBlockA j lvl) t) :
    StepMerkleARow pub R t domainForsNode
      (‹(lvl + 1) * 2 ^ 32 + j * 2 ^ (7 - lvl)› +ₚ ((stepRegsAt R t).kp *ₚ ‹2 ^ 16›)) := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨(stepBoolCheck_eq_zero_iff _).mp (gzz% hG 0), gz% hG 1,
    state12_ext12 (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 8) (gz% hG 3) (gz% hG 5)
      (gz% hG 7) (gz% hG 9) (gz% hG 10) (gz% hG 11) (gz% hG 12) (gz% hG 13), (regs% h)⟩

theorem stepSem_forsMerkleBlockB_inner {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {lvl : Nat} {isOdd : Bool} {t : Nat}
    (h : StepRowSem pub R (.forsMerkleBlockB lvl false isOdd) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with work := (stepPermAt R t).b0 } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), (regs% h)⟩

theorem stepSem_forsMerkleBlockB_even {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {lvl t : Nat} (h : StepRowSem pub R (.forsMerkleBlockB lvl true false) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    (stepRegsAt R t).cursor = Goldilocks.zero ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with curRoot := (stepPermAt R t).b0 } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), gzz% hG 12, (regs% h)⟩

theorem stepSem_forsMerkleBlockB_odd {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {lvl t : Nat} (h : StepRowSem pub R (.forsMerkleBlockB lvl true true) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    (stepRegsAt R t).cursor = Goldilocks.zero ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with work := (stepPermAt R t).b0 } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), gzz% hG 12, (regs% h)⟩

set_option maxHeartbeats 800000 in
theorem stepSem_forsRootsPairAbsorb {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {pair t : Nat} (h : StepRowSem pub R (.forsRootsPairAbsorb pair) t) :
    ((pair + 1 == 16) = true → ∀ s < 6, (stepRegsAt R t).rem.get s = Goldilocks.zero) ∧
    (R t).stIn =
      ⟨lane4Add (stepRegsAt R t).main.b0 (stepRegsAt R t).curRoot,
       lane4Add (stepRegsAt R t).main.b1 (stepRegsAt R t).work, (stepRegsAt R t).main.b2⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG : allZeroGoldilocks (stepOpGuardResiduals (.forsRootsPairAbsorb (pair + 1 == 16))
      (Goldilocks.ofNat 0) (stepOpRowInputsPerm pub (R t))) = true := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  cases hp : (pair + 1 == 16)
  · rw [hp] at hG
    exact ⟨fun hc => absurd hc (by simp),
      state12_ext12 (gz% hG 0) (gz% hG 3) (gz% hG 6) (gz% hG 9) (gz% hG 1) (gz% hG 4)
        (gz% hG 7) (gz% hG 10) (gz% hG 2) (gz% hG 5) (gz% hG 8) (gz% hG 11), (regs% h)⟩
  · rw [hp] at hG
    refine ⟨fun _ s hs => ?_,
      state12_ext12 (gz% hG 6) (gz% hG 9) (gz% hG 12) (gz% hG 15) (gz% hG 7) (gz% hG 10)
        (gz% hG 13) (gz% hG 16) (gz% hG 8) (gz% hG 11) (gz% hG 14) (gz% hG 17), (regs% h)⟩
    rcases s with _ | _ | _ | _ | _ | _ | s
    · exact gzz% hG 0
    · exact gzz% hG 1
    · exact gzz% hG 2
    · exact gzz% hG 3
    · exact gzz% hG 4
    · exact gzz% hG 5
    · exact absurd hs (by omega)

theorem stepSem_forsRootsFinalSqueeze {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .forsRootsFinalSqueeze t) :
    (R t).stIn = stepSqueezeIn (stepRegsAt R t) ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with curRoot := (stepPermAt R t).b0 } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), (regs% h)⟩

theorem stepSem_detTreeHmsgBlock0 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer t : Nat} (h : StepRowSem pub R (.detTreeHmsgBlock0 layer) t) :
    (R t).stIn =
      ⟨pub.1.pkSeed, pub.1.pkRoot,
       ⟨domainHMsgDetTree, ‹layer * 2 ^ 32› +ₚ (stepRegsAt R t).kp, (stepRegsAt R t).treeLo,
        (stepRegsAt R t).treeHi⟩⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 1) (gz% hG 3)
    (gz% hG 5) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), (regs% h)⟩

theorem stepSem_detTreeHmsgBlock1 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer t : Nat} (h : StepRowSem pub R (.detTreeHmsgBlock1 layer) t) :
    (∀ i < 32, stepAux R t i = Goldilocks.zero ∨ stepAux R t i = Goldilocks.one) ∧
    (R t).stIn =
      ⟨lane4Add (stepRegsAt R t).main.b0 (stepRegsAt R t).curRoot,
       ⟨(stepRegsAt R t).main.b1.x0 +ₚ stepWeightedSum (stepAux R t) (fun i => 2 ^ i) 32,
        (stepRegsAt R t).main.b1.x1 +ₚ Goldilocks.one,
        (stepRegsAt R t).main.b1.x2, (stepRegsAt R t).main.b1.x3⟩,
       (stepRegsAt R t).main.b2⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := stepRemZero
        main := stepPermAt R t
        acc := Goldilocks.zero } := by
  have hG := h.guard
  simp only [stepOpKindAndC0.public_eqs, stepOpGuardResiduals, allZeroGoldilocks_append,
    Bool.and_eq_true] at hG
  obtain ⟨⟨⟨hB, hRoot⟩, hSum⟩, hFrame⟩ := hG
  exact ⟨fun i hi => (stepBoolCheck_eq_zero_iff _).mp ((allZero_map_iff 32 _).mp hB i hi),
    state12_ext12 (gz% hRoot 0) (gz% hRoot 1) (gz% hRoot 2) (gz% hRoot 3)
      (gz% hSum 0) (gz% hSum 1) (gz% hFrame 0) (gz% hFrame 1) (gz% hFrame 2) (gz% hFrame 3)
      (gz% hFrame 4) (gz% hFrame 5), (regs% h)⟩

/-- `XmssMerkleBlockB` closing a non-top layer: the layer root moves to `ST_CUR_ROOT` and the
    64-bit tree index is shifted right by the subtree height (4 bits) into `kp_idx`. -/
theorem stepSem_xmssMerkleBlockB_link {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R (.xmssMerkleBlockB true false) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    (stepRegsAt R t).cursor = Goldilocks.zero ∧
    (∀ i < 4, stepAux R t i = Goldilocks.zero ∨ stepAux R t i = Goldilocks.one) ∧
    (∀ i < 14, (stepAux R t (4 + i)).val < 4) ∧
    (∀ i < 2, (stepAux R t (18 + i)).val < 4) ∧
    (∀ i < 14, (stepAux R t (20 + i)).val < 4) ∧
    (stepRegsAt R t).treeLo =
      stepWeightedSum (stepAux R t) (fun i => 2 ^ i) 4 +ₚ
        (stepWeightedSum (fun i => stepAux R t (4 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›) ∧
    (stepRegsAt R t).treeHi =
      stepWeightedSum (fun i => stepAux R t (18 + i)) (fun i => 4 ^ i) 2 +ₚ
        (stepWeightedSum (fun i => stepAux R t (20 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›) ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        curRoot := (stepPermAt R t).b0
        kp := stepWeightedSum (stepAux R t) (fun i => 2 ^ i) 4
        treeLo := stepWeightedSum (fun i => stepAux R t (4 + i)) (fun i => 4 ^ i) 14 +ₚ
          (stepWeightedSum (fun i => stepAux R t (18 + i)) (fun i => 4 ^ i) 2 *ₚ ‹2 ^ 28›)
        treeHi := stepWeightedSum (fun i => stepAux R t (20 + i)) (fun i => 4 ^ i) 14 } := by
  have hG := h.guard
  simp only [stepOpKindAndC0.public_eqs, stepOpGuardResiduals, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, allZeroGoldilocks_append, Bool.and_eq_true] at hG
  obtain ⟨hIn, ⟨⟨⟨⟨⟨hCursor, hB4⟩, hQa⟩, hQ2⟩, hQb⟩, hTree⟩⟩ := hG
  exact ⟨state12_ext12 (gz% hIn 0) (gz% hIn 1) (gz% hIn 2) (gz% hIn 3) (gz% hIn 4) (gz% hIn 5)
      (gz% hIn 6) (gz% hIn 7) (gz% hIn 8) (gz% hIn 9) (gz% hIn 10) (gz% hIn 11), gzz% hCursor 0,
    fun i hi => (stepBoolCheck_eq_zero_iff _).mp ((allZero_map_iff 4 _).mp hB4 i hi),
    fun i hi => (quarticBase4_eq_zero_iff _).mp ((allZero_map_iff 14 _).mp hQa i hi),
    fun i hi => (quarticBase4_eq_zero_iff _).mp ((allZero_map_iff 2 _).mp hQ2 i hi),
    fun i hi => (quarticBase4_eq_zero_iff _).mp ((allZero_map_iff 14 _).mp hQb i hi),
    gz% hTree 0, gz% hTree 1, (regs% h)⟩


/-- Executable decision and witness extraction for an active XMSS slot. The success branch
    contains the native signature itself, not an existential proposition requiring choice. -/
def extractXmssSlotOrReject (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .xmssPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    PSum { sig : AggNativeSignature // verifyAggNativeSig xmssPoseidon2Geom pub.1 msg sig = true }
      (stepOp256TableOk .xmssPoseidon2 slots rows = false) :=
  if h : stepOp256TableOk .xmssPoseidon2 slots rows = true then
    .inl ⟨stepXmssSig (stepOpSlotRow .xmssPoseidon2 rows k),
      stepOp256TableOk_xmss_extract slots rows k pub msg h hSlot hProf hMu⟩
  else .inr (Bool.eq_false_iff.mpr h)

/-- The active slots for a public committee statement bind both key and message digest. -/
def xmssCommitteeSlots (stmt : AggArithPublicStmt) : List StepOpSlot :=
  stmt.committeePks.map (fun pk => some (pk, computeMessageMu pk stmt.msg))

/-- Read every signature from its accepted machine block in committee order. -/
def xmssCommitteeSigs (stmt : AggArithPublicStmt) (rows : List StepOpRow) :
    List AggNativeSignature :=
  (List.range stmt.committeePks.length).map
    (fun k => stepXmssSig (stepOpSlotRow .xmssPoseidon2 rows k))

/-- Whole-committee soundness of the XMSS machine extractor. -/
theorem xmssCommitteeSigs_valid (stmt : AggArithPublicStmt) (rows : List StepOpRow)
    (hGeom : stmt.geom = xmssPoseidon2Geom) (hWf : stmt.wellFormed = true)
    (hTable : stepOp256TableOk .xmssPoseidon2 (xmssCommitteeSlots stmt) rows = true) :
    (xmssCommitteeSigs stmt rows).length = stmt.committeePks.length ∧
    ∀ (k : Nat) (hkP : k < stmt.committeePks.length)
      (hkS : k < (xmssCommitteeSigs stmt rows).length),
      verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg
        ((xmssCommitteeSigs stmt rows)[k]'hkS) = true := by
  refine ⟨by simp [xmssCommitteeSigs], ?_⟩
  intro k hkP hkS
  have hpks : stmt.committeePks.all (·.profile == stmt.geom.profile) = true :=
    (Bool.and_eq_true_iff.mp hWf).2
  have hp : (stmt.committeePks[k]'hkP).profile = .xmssPoseidon2 := by
    have h := eq_of_beq (List.all_eq_true.mp hpks _ (List.getElem_mem hkP))
    simpa only [hGeom, xmssPoseidon2Geom.public_eqs] using h
  have hs : (xmssCommitteeSlots stmt)[k]? =
      some (some (stmt.committeePks[k]'hkP, computeMessageMu (stmt.committeePks[k]'hkP) stmt.msg)) := by
    simp [xmssCommitteeSlots, List.getElem?_eq_getElem hkP]
  simpa [xmssCommitteeSigs, hGeom] using
    stepOp256TableOk_xmss_extract (xmssCommitteeSlots stmt) rows k
      (stmt.committeePks[k]'hkP, computeMessageMu (stmt.committeePks[k]'hkP) stmt.msg)
      stmt.msg hTable hs hp rfl

/-- Construct the serialized trace from the machine-extracted signatures. Its 14 boundary
    columns and serialized witness blocks are checked by the existing row constraints. -/
def xmssMachineToExecutionTrace (stmt : AggArithPublicStmt) (rows : List StepOpRow) :
    AggExecutionTrace := buildHonestAggExecutionTrace stmt (xmssCommitteeSigs stmt rows)

theorem xmssMachineToExecutionTrace_accepts (stmt : AggArithPublicStmt) (rows : List StepOpRow)
    (hGeom : stmt.geom = xmssPoseidon2Geom) (hWf : stmt.wellFormed = true)
    (hTable : stepOp256TableOk .xmssPoseidon2 (xmssCommitteeSlots stmt) rows = true) :
    traceSatisfiesAllConstraints stmt (xmssMachineToExecutionTrace stmt rows) = true := by
  obtain ⟨hLen, hAll⟩ := xmssCommitteeSigs_valid stmt rows hGeom hWf hTable
  exact buildHonestAggExecutionTrace_satisfies_constraints stmt _ hWf hLen hAll


/-! ### §3.15. Stateless derive rows: FORS indices and the 64-bit leaf index -/

/-- Row `t0 + i` of a run executes the `i`-th opcode of the run. -/


private theorem g_ofNat_inj {a b : Nat} (ha : a < goldilocksPrime) (hb : b < goldilocksPrime)
    (h : (‹a› : Goldilocks) = ‹b›) : a = b := by
  have hv := congrArg Goldilocks.val h
  rw [Goldilocks.ofNat_val, Goldilocks.ofNat_val, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
  exact hv

/-- Four consecutive base-4 digits are one base-256 digit. -/
private theorem nat_byte_of_quads (v s : Nat) :
    (v / 4 ^ (4 * s)) % 4 + (v / 4 ^ (4 * s + 1)) % 4 * 4 + (v / 4 ^ (4 * s + 2)) % 4 * 16 +
      (v / 4 ^ (4 * s + 3)) % 4 * 64 = (v / 256 ^ s) % 256 := by
  have e0 : 4 ^ (4 * s) = 256 ^ s := by rw [Nat.pow_mul]
  have e1 : v / 4 ^ (4 * s + 1) = v / 256 ^ s / 4 := by
    rw [Nat.pow_succ, e0, Nat.div_div_eq_div_mul]
  have e2 : v / 4 ^ (4 * s + 2) = v / 256 ^ s / 16 := by
    rw [Nat.pow_add, e0, Nat.div_div_eq_div_mul]
  have e3 : v / 4 ^ (4 * s + 3) = v / 256 ^ s / 64 := by
    rw [Nat.pow_add, e0, Nat.div_div_eq_div_mul]
  rw [e0, e1, e2, e3]
  generalize v / 256 ^ s = w
  omega

/-- A weighted sum of the low `n` base-`B` digits of `w` is `w` without its high part. -/
private theorem stepWeightedNat_digits (B w : Nat) (f : Nat → Goldilocks)
    (hB : B ≤ goldilocksPrime) (hB0 : 0 < B) :
    ∀ n, (∀ i < n, f i = ‹(w / B ^ i) % B›) →
      stepWeightedNat f (fun i => B ^ i) n + B ^ n * (w / B ^ n) = w
  | 0, _ => by
    rw [Nat.pow_zero, Nat.div_one, Nat.one_mul]
    exact Nat.zero_add w
  | n + 1, h => by
    have ih := stepWeightedNat_digits B w f hB hB0 n (fun i hi => h i (by omega))
    have hd : (w / B ^ n) % B < goldilocksPrime :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ hB0) hB
    have hq := Nat.div_add_mod (w / B ^ n) B
    have key : w / B ^ n % B * B ^ n + B ^ n * B * (w / B ^ n / B) = B ^ n * (w / B ^ n) := by
      rw [Nat.mul_comm (w / B ^ n % B) (B ^ n), Nat.mul_assoc, ← Nat.mul_add, Nat.add_comm, hq]
    rw [stepWeightedNat_succ, h n (by omega), Goldilocks.ofNat_val, Nat.mod_eq_of_lt hd,
      Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.add_assoc, key]
    exact ih

/-- A weighted sum of `n` base-`B` digits is below `B ^ n`. -/
private theorem stepWeightedNat_lt (B : Nat) (f : Nat → Goldilocks) :
    ∀ n, (∀ i < n, (f i).val < B) → stepWeightedNat f (fun i => B ^ i) n < B ^ n
  | 0, _ => Nat.le_of_ble_eq_true rfl
  | n + 1, h => by
    have ih := stepWeightedNat_lt B f n (fun i hi => h i (by omega))
    have hd := h n (by omega)
    have h1 : ((f n).val + 1) * B ^ n ≤ B * B ^ n := Nat.mul_le_mul_right _ hd
    rw [Nat.succ_mul] at h1
    rw [stepWeightedNat_succ, Nat.pow_succ, Nat.mul_comm (B ^ n) B]
    omega

/-- Limb `l` of the seven limbs the stateless XOF squeezes. -/
def stepXofLimb (m : Poseidon2State12) : Nat → Goldilocks
  | 0 => m.b0.x0
  | 1 => m.b0.x1
  | 2 => m.b0.x2
  | 3 => m.b0.x3
  | 4 => m.b1.x0
  | 5 => m.b1.x1
  | _ => m.b1.x2

/-- FORS leaf index of tree `t`: byte `t % 7` of squeezed limb `t / 7`. -/
def stepForsIdx (m : Poseidon2State12) (t : Nat) : Nat :=
  ((stepXofLimb m (t / 7)).val / 256 ^ (t % 7)) % 256

private theorem stepForsIdx_lt (m : Poseidon2State12) (t : Nat) : stepForsIdx m t < 256 :=
  Nat.mod_lt _ (by decide)

/-- The 64-bit global leaf index: the low 32 bits of limbs 5 and 6. -/
def stepXofLeaf (m : Poseidon2State12) : Nat :=
  (m.b1.x1.val % 2 ^ 32) + (m.b1.x2.val % 2 ^ 32) * 2 ^ 32

/-- The stateless XOF state of a signer block: `rRand` is read from the auxiliary cells of
    the `StatelessDeriveBlock1` row. -/
def stepXofState (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow) : Poseidon2State12 :=
  statelessXofSpongeState pub.1 (stepAuxLane R 1 0) pub.2

/-- The FORS packing fold of a `StatelessDecompLimb` row computes the base-256 packing of the
    bytes it reads. -/
private theorem stepForsPack_field (x : StepOpRowInputs) (bv : Nat → Nat) (firstJ s : Nat) :
    ∀ (subs : List Nat) (A : Nat),
      (∀ sub ∈ subs, stepByteVal x sub = ‹bv (firstJ + sub)›) →
      subs.foldl (fun acc sub =>
          if stRemPack + (firstJ + sub) / 6 = stRemPack + s then
            acc +ₚ (stepByteVal x sub *ₚ ‹2 ^ (8 * ((firstJ + sub) % 6))›)
          else acc) ‹A› =
        ‹stepPackFoldG 256 (fun c => c / 6) (fun s' => 6 * s') bv s
          (subs.map (fun sub => firstJ + sub)) A›
  | [], _, _ => rfl
  | sub :: rest, A, h => by
    have hB := h sub (List.mem_cons_self ..)
    have ih := fun A' => stepForsPack_field x bv firstJ s rest A'
      (fun j hj => h j (List.mem_cons_of_mem _ hj))
    rw [List.foldl_cons, List.map_cons]
    unfold stepPackFoldG
    rw [List.foldl_cons]
    by_cases hc : (firstJ + sub) / 6 = s
    · simp only [hc, ↓reduceIte]
      have hE : (firstJ + sub) % 6 = firstJ + sub - 6 * s := by omega
      have hStep : (‹A› : Goldilocks) +ₚ
          (stepByteVal x sub *ₚ ‹2 ^ (8 * ((firstJ + sub) % 6))›) =
          ‹A + bv (firstJ + sub) * 256 ^ (firstJ + sub - 6 * s)› := by
        rw [hB, ← g_ofNat_mul, ← g_ofNat_add, hE, Nat.pow_mul]
      rw [hStep]
      exact ih _
    · have hcond : ¬ (stRemPack + (firstJ + sub) / 6 = stRemPack + s) :=
        fun h' => hc (Nat.add_left_cancel h')
      simp only [hcond, hc, ↓reduceIte]
      exact ih _

private theorem stepForsIdx_eq (m : Poseidon2State12) (l sub : Nat) (hs : sub < 7) :
    stepForsIdx m (7 * l + sub) = ((stepXofLimb m l).val / 256 ^ sub) % 256 := by
  unfold stepForsIdx
  rw [show (7 * l + sub) / 7 = l by omega, show (7 * l + sub) % 7 = sub by omega]

/-- **`StatelessDecompLimb l` row, `l < 5`.** The limb is `< 2^63`, and its low bytes are added
    to the `ST_REM_PACK` limbs as the FORS indices of the trees it owns. -/
theorem stepStatelessPack_row {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow} {l t : Nat}
    (hl : l < 5) (h : StepRowSem pub R (.statelessDecompLimb l) t) (A : Nat → Nat)
    (hRem : ∀ s < 6, (stepRegsAt R t).rem.get s = ‹A s›) :
    (stepXofLimb (stepRegsAt R t).main l).val < 2 ^ 63 ∧
    (∀ s < 6, (stepRegsAt R (t + 1)).rem.get s =
      ‹stepPackFoldG 256 (fun c => c / 6) (fun s' => 6 * s') (stepForsIdx (stepRegsAt R t).main) s
        (List.range' (7 * l) (if l < 4 then 7 else 4)) (A s)›) ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with rem := (stepRegsAt R (t + 1)).rem } := by
  obtain ⟨hD, hR⟩ := stepSem_statelessDecompLimb_pack hl h
  obtain ⟨hLt, hAux, _⟩ := (stepLimb63Decomp_allZero_iff _ l).mp hD
  have hLimb : (stepOpRowInputsPerm pub (R t)).prev (stMainSponge + l) =
      stepXofLimb (stepRegsAt R t).main l := by
    rcases l with _ | _ | _ | _ | _ | l
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hl (by omega)
  rw [hLimb] at hLt hAux
  have hByte : ∀ sub < 7, stepByteVal (stepOpRowInputsPerm pub (R t)) sub =
      ‹stepForsIdx (stepRegsAt R t).main (7 * l + sub)› := by
    intro sub hs
    simp only [stepByteVal_eq]
    rw [hAux (4 * sub) (by omega), hAux (4 * sub + 1) (by omega), hAux (4 * sub + 2) (by omega),
      hAux (4 * sub + 3) (by omega), ← g_ofNat_mul, ← g_ofNat_mul, ← g_ofNat_mul, ← g_ofNat_add,
      ← g_ofNat_add, ← g_ofNat_add, stepForsIdx_eq _ l sub hs]
    exact congrArg Goldilocks.ofNat (nat_byte_of_quads _ _)
  have hRemE : ∀ s < 6,
      stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l (stRemPack + s) =
      ‹stepPackFoldG 256 (fun c => c / 6) (fun s' => 6 * s') (stepForsIdx (stepRegsAt R t).main) s
        (List.range' (7 * l) (if l < 4 then 7 else 4)) (A s)› := by
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
    by_cases h4 : l < 4
    · simp only [stepStatelessDecompExpected.public_eqs, stepForsPackExpected.public_eqs]
      simp only [h4, ↓reduceIte]
      rw [hPrev, range'_eq_map]
      exact stepForsPack_field _ _ (7 * l) s (List.range 7) (A s)
        (fun sub hsub => hByte sub (List.mem_range.mp hsub))
    · have e4 : l = 4 := by omega
      subst e4
      simp only [stepStatelessDecompExpected.public_eqs, Nat.reduceLT, ↓reduceIte]
      show stepForsPackExpected (stepOpRowInputsPerm pub (R t)) 28 4 (stRemPack + s) =
        ‹stepPackFoldG 256 (fun c => c / 6) (fun s' => 6 * s') (stepForsIdx (stepRegsAt R t).main) s
          (List.range' 28 4) (A s)›
      simp only [stepForsPackExpected.public_eqs]
      rw [hPrev, range'_eq_map]
      exact stepForsPack_field _ _ 28 s (List.range 4) (A s)
        (fun sub hsub => hByte sub (by have := List.mem_range.mp hsub; omega))
  have hRemGet : ∀ s < 6, (stepRegsAt R (t + 1)).rem.get s =
      stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l (stRemPack + s) := by
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
  refine ⟨hLt, fun s hs => (hRemGet s hs).trans (hRemE s hs), ?_⟩
  rw [hR]

private theorem range'_32_split :
    List.range' 0 32 =
      List.range' 0 7 ++ List.range' 7 7 ++ List.range' 14 7 ++ List.range' 21 7 ++
        List.range' 28 4 := by
  decide

/-- The two low base-4 digits of a decomposed limb are its low four bits. -/
private theorem stepLow4_eq (x : StepOpRowInputs) (v : Nat)
    (hAux : ∀ i < 31, x.aux i = ‹(v / 4 ^ i) % 4›) :
    x.aux 0 +ₚ (x.aux 1 *ₚ ‹4›) = ‹v % 16› := by
  have a0 := hAux 0 (by decide)
  have a1 := hAux 1 (by decide)
  rw [Nat.pow_zero, Nat.div_one] at a0
  rw [Nat.pow_one] at a1
  rw [a0, a1, ← g_ofNat_mul, ← g_ofNat_add]
  exact congrArg Goldilocks.ofNat (by omega)

/-- Digits 2..15 of a decomposed limb are bits 4..31 of the limb. -/
private theorem stepHi28_eq (x : StepOpRowInputs) (v : Nat)
    (hAux : ∀ i < 31, x.aux i = ‹(v / 4 ^ i) % 4›) :
    stepHi28 x = ‹(v / 16) % 4 ^ 14› := by
  simp only [stepHi28_def]
  rw [stepWeightedSum_eq_ofNat]
  have hS := stepWeightedNat_digits 4 (v / 16) (fun i => x.aux (2 + i)) (by decide) (by decide)
    14 (fun i hi => by
      show x.aux (2 + i) = _
      rw [hAux (2 + i) (by omega), Nat.pow_add, Nat.div_div_eq_div_mul])
  have hL := stepWeightedNat_lt 4 (fun i => x.aux (2 + i)) 14 (fun i hi => by
    show (x.aux (2 + i)).val < 4
    rw [hAux (2 + i) (by omega), Goldilocks.ofNat_val]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide)))
  exact congrArg Goldilocks.ofNat (by omega)

/-- The nine rows of the stateless derive. -/
def stepDeriveOps : List StepOp :=
  [StepOp.statelessDeriveBlock0, StepOp.statelessDeriveBlock1] ++
    (List.range 7).map StepOp.statelessDecompLimb

/-- **Stateless derive rows.** The nine rows `StatelessDeriveBlock0 .. StatelessDecompLimb 6`
    check that the seven squeezed limbs of the stateless XOF are `< 2^63`, leave in each
    `ST_REM_PACK` limb the base-256 packing of the FORS indices of the trees it owns, and load
    the address registers with the split `(leaf % 16, leaf / 16)` of the global leaf index. -/
theorem stepStatelessDerive_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    (hRun : StepRunAt pub R stepDeriveOps 0) :
    (∀ l < 7, (stepXofLimb (stepXofState pub R) l).val < 2 ^ 63) ∧
    (∀ s < 6, (stepRegsAt R 9).rem.get s =
      ‹stepPackFoldG 256 (fun c => c / 6) (fun s' => 6 * s') (stepForsIdx (stepXofState pub R)) s
        (List.range' 0 32) 0›) ∧
    StepAddrOk (stepRegsAt R 9) (stepXofLeaf (stepXofState pub R) % 16)
      (stepXofLeaf (stepXofState pub R) / 16) := by
  have hz : (‹0› : Goldilocks) = Goldilocks.zero := Goldilocks.ext rfl
  have h0 : StepRowSem pub R .statelessDeriveBlock0 0 := hRun.get 0 _ rfl
  have h1 : StepRowSem pub R .statelessDeriveBlock1 1 := hRun.get 1 _ rfl
  have d0 : StepRowSem pub R (.statelessDecompLimb 0) 2 := hRun.get 2 _ rfl
  have d1 : StepRowSem pub R (.statelessDecompLimb 1) 3 := hRun.get 3 _ rfl
  have d2 : StepRowSem pub R (.statelessDecompLimb 2) 4 := hRun.get 4 _ rfl
  have d3 : StepRowSem pub R (.statelessDecompLimb 3) 5 := hRun.get 5 _ rfl
  have d4 : StepRowSem pub R (.statelessDecompLimb 4) 6 := hRun.get 6 _ rfl
  have d5 : StepRowSem pub R (.statelessDecompLimb 5) 7 := hRun.get 7 _ rfl
  have d6 : StepRowSem pub R (.statelessDecompLimb 6) 8 := hRun.get 8 _ rfl
  obtain ⟨hIn0, hR1⟩ := stepSem_statelessDeriveBlock0 h0
  obtain ⟨hIn1, hR2⟩ := stepSem_statelessDeriveBlock1 h1
  have hR1' : stepRegsAt R 1 = _ := hR1
  have hR2' : stepRegsAt R 2 = _ := hR2
  have hM1 : (stepRegsAt R 1).main = poseidon2Perm12 (R 0).stIn := by rw [hR1']; rfl
  have hM2 : (stepRegsAt R 2).main = stepXofState pub R := by
    have e : (stepRegsAt R 2).main = poseidon2Perm12 (R 1).stIn := by rw [hR2']; rfl
    rw [e, hIn1, hM1, hIn0]
    simp only [stepXofState, statelessXofSpongeState.public_eqs]
  have hRem2 : ∀ s < 6, (stepRegsAt R 2).rem.get s = ‹(fun _ => 0) s› := by
    intro s hs
    rw [hR2']
    rcases s with _ | _ | _ | _ | _ | _ | s
    · exact hz.symm
    · exact hz.symm
    · exact hz.symm
    · exact hz.symm
    · exact hz.symm
    · exact hz.symm
    · exact absurd hs (by omega)
  obtain ⟨l0, r0, f0⟩ := stepStatelessPack_row (by decide) d0 (fun _ => 0) hRem2
  have f0' : stepRegsAt R 3 = _ := f0
  rw [hM2] at l0 r0
  simp only [Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r0
  have m3 : (stepRegsAt R 3).main = stepXofState pub R := by rw [f0']; exact hM2
  obtain ⟨l1, r1, f1⟩ := stepStatelessPack_row (by decide) d1 _ r0
  have f1' : stepRegsAt R 4 = _ := f1
  rw [m3] at l1 r1
  simp only [Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r1
  have m4 : (stepRegsAt R 4).main = stepXofState pub R := by rw [f1']; exact m3
  obtain ⟨l2, r2, f2⟩ := stepStatelessPack_row (by decide) d2 _ r1
  have f2' : stepRegsAt R 5 = _ := f2
  rw [m4] at l2 r2
  simp only [Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r2
  have m5 : (stepRegsAt R 5).main = stepXofState pub R := by rw [f2']; exact m4
  obtain ⟨l3, r3, f3⟩ := stepStatelessPack_row (by decide) d3 _ r2
  have f3' : stepRegsAt R 6 = _ := f3
  rw [m5] at l3 r3
  simp only [Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r3
  have m6 : (stepRegsAt R 6).main = stepXofState pub R := by rw [f3']; exact m5
  obtain ⟨l4, r4, f4⟩ := stepStatelessPack_row (by decide) d4 _ r3
  have f4' : stepRegsAt R 7 = _ := f4
  rw [m6] at l4 r4
  simp only [Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r4
  have m7 : (stepRegsAt R 7).main = stepXofState pub R := by rw [f4']; exact m6
  obtain ⟨hD5, hR8⟩ := stepSem_statelessDecompLimb5 d5
  have hR8' : stepRegsAt R 8 = _ := hR8
  have m8 : (stepRegsAt R 8).main = stepXofState pub R := by rw [hR8']; exact m7
  obtain ⟨hD6, hR9⟩ := stepSem_statelessDecompLimb6 d6
  have hR9' : stepRegsAt R 9 = _ := hR9
  obtain ⟨hLt5, hAux5, _⟩ := (stepLimb63Decomp_allZero_iff _ 5).mp hD5
  obtain ⟨hLt6, hAux6, _⟩ := (stepLimb63Decomp_allZero_iff _ 6).mp hD6
  have hL5 : (stepOpRowInputsPerm pub (R 7)).prev (stMainSponge + 5) =
      (stepXofState pub R).b1.x1 := by
    rw [← m7]; rfl
  have hL6 : (stepOpRowInputsPerm pub (R 8)).prev (stMainSponge + 6) =
      (stepXofState pub R).b1.x2 := by
    rw [← m8]; rfl
  rw [hL5] at hLt5 hAux5
  rw [hL6] at hLt6 hAux6
  have hKp8 : (stepRegsAt R 8).kp = ‹(stepXofState pub R).b1.x1.val % 16› := by
    rw [hR8']
    exact stepLow4_eq _ _ hAux5
  have hLo8 : (stepRegsAt R 8).treeLo = ‹((stepXofState pub R).b1.x1.val / 16) % 4 ^ 14› := by
    rw [hR8']
    exact stepHi28_eq _ _ hAux5
  have hHi8 : (stepRegsAt R 8).treeHi = (stepRegsAt R 7).treeHi := by rw [hR8']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    · exact l0
    · exact l1
    · exact l2
    · exact l3
    · exact l4
    · exact hLt5
    · exact hLt6
    · exact absurd hl (by omega)
  · intro s hs
    have e9 : (stepRegsAt R 9).rem = (stepRegsAt R 7).rem := by rw [hR9', hR8']
    rw [e9, range'_32_split, stepPackFoldG_append, stepPackFoldG_append, stepPackFoldG_append,
      stepPackFoldG_append]
    exact r4 s hs
  · have e : (stepRegsAt R 9).kp = (stepRegsAt R 8).kp := by rw [hR9']
    rw [e, hKp8]
    exact congrArg Goldilocks.ofNat (by unfold stepXofLeaf; omega)
  · have e : (stepRegsAt R 9).treeLo = (stepRegsAt R 8).treeLo +ₚ
        ((stepAux R 8 0 +ₚ (stepAux R 8 1 *ₚ ‹4›)) *ₚ ‹2 ^ 28›) := by rw [hR9']
    have e2 : stepAux R 8 0 +ₚ (stepAux R 8 1 *ₚ ‹4›) =
        ‹(stepXofState pub R).b1.x2.val % 16› := stepLow4_eq _ _ hAux6
    rw [e, e2, hLo8, ← g_ofNat_mul, ← g_ofNat_add]
    exact congrArg Goldilocks.ofNat (by unfold stepXofLeaf; omega)
  · have e : (stepRegsAt R 9).treeHi = stepHi28 (stepOpRowInputsPerm pub (R 8)) := by rw [hR9']
    rw [e, stepHi28_eq _ _ hAux6]
    exact congrArg Goldilocks.ofNat (by unfold stepXofLeaf; omega)

/-! ### §3.16. FORS rows: 32 openings and the sponge of their roots -/

/-- The 17 rows of one FORS tree: the leaf hash, then per level one `ForsMerkleBlockA` and one
    `ForsMerkleBlockB` row. -/
def stepForsTreeOps (j : Nat) (odd : Bool) : List StepOp :=
  [StepOp.forsLeafHash j (j / 6)] ++
  (List.range 8).flatMap (fun lvl =>
    [StepOp.forsMerkleBlockA j lvl, StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) odd])

/-- The FORS leaf index read from the four base-4 digits of a `ForsLeafHash` row. -/
def stepForsIdxN (R : Nat → StepOpRow) (t : Nat) : Nat :=
  stepWeightedNat (fun k => stepAux R t (4 + k)) (fun k => 4 ^ k) 4

/-- The FORS opening read from the rows of a tree whose `ForsLeafHash` row is `T`. -/
def stepForsOpening (R : Nat → StepOpRow) (T : Nat) : AggForsTreeOpening :=
  ⟨stepAuxLane R T 0, (List.range 8).map (fun l => stepAuxLane R (T + 1 + 2 * l) 2)⟩

/-- The FORS node address limb of the rows equals the native node address. -/
private theorem stepNodeHashF_fors (pkSeed : Lane4) (tree kpN j l par : Nat) (L Rr : Lane4)
    (hk : kpN < 16) (hj : j < 32) (hl : l < 8) (hp : par < 256) :
    stepNodeHashF domainForsNode
        ((‹(l + 1) * 2 ^ 32 + j * 2 ^ (7 - l)› +ₚ (‹kpN› *ₚ ‹2 ^ 16›)) +ₚ ‹par›)
        ‹tree % 2 ^ 32› ‹(tree / 2 ^ 32) % 2 ^ 32› pkSeed L Rr =
      merkleAddrNodeHash domainForsNode pkSeed 0 tree (forsNodeAddr 8 kpN j) (1 + l) par L Rr := by
  have hMeta : (‹(l + 1) * 2 ^ 32 + j * 2 ^ (7 - l)› +ₚ (‹kpN› *ₚ ‹2 ^ 16›)) +ₚ ‹par› =
      ‹(0 % 65536) * 2 ^ 48 + ((1 + l) % 65536) * 2 ^ 32 +
        (forsNodeAddr 8 kpN j (1 + l) par % 2 ^ 32)› := by
    rw [← g_ofNat_mul, ← g_ofNat_add, ← g_ofNat_add]
    refine congrArg Goldilocks.ofNat ?_
    simp only [forsNodeAddr.public_eqs]
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, show 8 - (1 + l) = 7 - l by omega]
    have hX : j * 2 ^ (7 - l) ≤ 31 * 2 ^ 7 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  simp only [merkleAddrNodeHash.public_eqs, merkleNodeHash.public_eqs, stepNodeHashF.public_eqs]
  rw [hMeta]

/-- What the 17 rows of FORS tree `j` starting at row `T` establish. -/
structure StepForsTreeFacts (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (kpN tree j : Nat) (odd : Bool) (T : Nat) : Prop where
  idxLt : stepForsIdxN R T < 256
  get : (stepRegsAt R T).rem.get (j / 6) =
    ‹stepForsIdxN R T› +ₚ (stepAux R T 8 *ₚ ‹256›)
  set : (stepRegsAt R (T + 17)).rem = (stepRegsAt R T).rem.set (j / 6) (stepAux R T 8)
  root : merkleWalkRoot domainForsNode pub.1.pkSeed 0 tree (forsNodeAddr 8 kpN j) 1
      (stepForsIdxN R T)
      (poseidon2Compress12FF (stepAuxLane R T 0) pub.1.pkSeed
        ⟨domainForsLeaf, ‹(kpN <<< 24) ||| ((j <<< 8) ||| stepForsIdxN R T)›,
         ‹tree % 2 ^ 32›, ‹(tree / 2 ^ 32) % 2 ^ 32›⟩)
      ((List.range 8).map (fun l => stepAuxLane R (T + 1 + 2 * l) 2)) =
    (stepPermAt R (T + 16)).b0
  kp : (stepRegsAt R (T + 17)).kp = (stepRegsAt R T).kp
  treeLo : (stepRegsAt R (T + 17)).treeLo = (stepRegsAt R T).treeLo
  treeHi : (stepRegsAt R (T + 17)).treeHi = (stepRegsAt R T).treeHi
  main : (stepRegsAt R (T + 17)).main = (stepRegsAt R T).main
  outE : odd = false → (stepRegsAt R (T + 17)).curRoot = (stepPermAt R (T + 16)).b0
  outO : odd = true → (stepRegsAt R (T + 17)).work = (stepPermAt R (T + 16)).b0 ∧
    (stepRegsAt R (T + 17)).curRoot = (stepRegsAt R T).curRoot

/-- **FORS tree rows.** The 17 rows of one tree hash the opened leaf under the tree's leaf
    address, walk its authentication path under the tree's node addresses, and consume one
    byte of the packed indices. -/
theorem stepForsTree_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {j kpN tree T : Nat} {odd : Bool}
    (hRun : StepRunAt pub R (stepForsTreeOps j odd) T)
    (hAddr : StepAddrOk (stepRegsAt R T) kpN tree) (hk : kpN < 16) (hj : j < 32) :
    StepForsTreeFacts pub R kpN tree j odd T := by
  have hLeaf : StepRowSem pub R (.forsLeafHash j (j / 6)) T := hRun.append_left.head
  have hLvRun : StepRunAt pub R ((List.range 8).flatMap (fun lvl =>
      [StepOp.forsMerkleBlockA j lvl, StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) odd]))
      (T + 1) := hRun.append_right
  have hLv := StepRunAt.flatMap_range (L := 2) (fun _ => rfl) 8 hLvRun
  have hArow : ∀ l < 8, StepRowSem pub R (.forsMerkleBlockA j l) (T + 1 + 2 * l) := by
    intro l hl
    have h := (hLv l hl).head
    rw [Nat.mul_comm l 2] at h
    exact h
  have hBrow : ∀ l < 8,
      StepRowSem pub R (.forsMerkleBlockB l (l + 1 == 8) odd) (T + 1 + 2 * l + 1) := by
    intro l hl
    have h := (hLv l hl).tail.head
    rw [Nat.mul_comm l 2] at h
    exact h
  obtain ⟨hDig, hGet, hInL, hRL⟩ := stepSem_forsLeafHash (by omega : j / 6 < 6) hLeaf
  have hRL' : stepRegsAt R (T + 1) = _ := hRL
  have hIdxEq : stepForsIdxF R T = ‹stepForsIdxN R T› := stepWeightedSum_eq_ofNat _ _ _
  have hIdxLt : stepForsIdxN R T < 256 := stepWeightedNat_lt 4 _ 4 hDig
  have hLast : StepRowSem pub R (.forsMerkleBlockB 7 true odd) (T + 16) := hBrow 7 (by decide)
  have hLastFacts : (R (T + 16)).stIn = stepMerkleBIn (stepRegsAt R (T + 16)) ∧
      (stepRegsAt R (T + 16)).cursor = Goldilocks.zero := by
    cases odd
    · obtain ⟨a, b, _⟩ := stepSem_forsMerkleBlockB_even hLast
      exact ⟨a, b⟩
    · obtain ⟨a, b, _⟩ := stepSem_forsMerkleBlockB_odd hLast
      exact ⟨a, b⟩
  have hInner : ∀ l, l < 7 →
      (R (T + 1 + 2 * l + 1)).stIn = stepMerkleBIn (stepRegsAt R (T + 1 + 2 * l + 1)) ∧
      stepRegsAt R (T + 1 + 2 * l + 2) =
        { stepRegsAt R (T + 1 + 2 * l + 1) with
          work := (stepPermAt R (T + 1 + 2 * l + 1)).b0 } := by
    intro l hl
    have h := hBrow l (by omega)
    rw [beq_false_of_ne (by omega : l + 1 ≠ 8)] at h
    exact stepSem_forsMerkleBlockB_inner h
  have kp1 : (stepRegsAt R (T + 1)).kp = (stepRegsAt R T).kp := by rw [hRL']
  have lo1 : (stepRegsAt R (T + 1)).treeLo = (stepRegsAt R T).treeLo := by rw [hRL']
  have hi1 : (stepRegsAt R (T + 1)).treeHi = (stepRegsAt R T).treeHi := by rw [hRL']
  have main1 : (stepRegsAt R (T + 1)).main = (stepRegsAt R T).main := by rw [hRL']
  have cur1 : (stepRegsAt R (T + 1)).curRoot = (stepRegsAt R T).curRoot := by rw [hRL']
  have rem1 : (stepRegsAt R (T + 1)).rem = (stepRegsAt R T).rem.set (j / 6) (stepAux R T 8) := by
    rw [hRL']
  have hFr : ∀ l, l ≤ 7 →
      StepFrameSWC (stepRegsAt R (T + 1 + 2 * l)) (stepRegsAt R (T + 1)) := by
    intro l
    induction l with
    | zero => intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | succ l ih =>
      intro hl
      have iF := ih (by omega)
      have hA := (stepMerkleARow_fors (hArow l (by omega))).next
      have hB := (hInner l (by omega)).2
      have e : T + 1 + 2 * (l + 1) = T + 1 + 2 * l + 2 := by omega
      rw [e, hB, hA]
      exact ⟨iF.curRoot, iF.kp, iF.treeLo, iF.treeHi, iF.rem, iF.main⟩
  have hKpRow : ∀ l < 8, (stepRegsAt R (T + 1 + 2 * l)).kp = ‹kpN› :=
    fun l hl => ((hFr l (by omega)).kp.trans kp1).trans hAddr.kp
  have hA' : ∀ l < 8, StepMerkleARow pub R (T + 1 + 2 * l) domainForsNode
      (‹(l + 1) * 2 ^ 32 + j * 2 ^ (7 - l)› +ₚ (‹kpN› *ₚ ‹2 ^ 16›)) := by
    intro l hl
    have h := stepMerkleARow_fors (hArow l hl)
    rw [hKpRow l hl] at h
    exact h
  obtain ⟨_, hWalk, hFr16⟩ := stepMerkle_sem (layerV := 0) (treeV := tree)
    (addr := forsNodeAddr 8 kpN j) (idx0 := stepForsIdxN R T) (t1 := T + 1) (h := 8) hA'
    (fun l hl => by
      by_cases h7 : l < 7
      · exact (hInner l h7).1
      · have e : l = 7 := by omega
        subst e
        exact hLastFacts.1)
    (fun l hl => (hInner l (by omega)).2)
    hLastFacts.2
    (by rw [hRL']; exact hIdxEq)
    (by omega) (by decide) (by decide)
    (fun l hl _ L Rr => by
      rw [lo1, hi1, hAddr.lo, hAddr.hi]
      exact stepNodeHashF_fors pub.1.pkSeed tree kpN j l (stepForsIdxN R T / 2 ^ (l + 1)) L Rr
        hk hj hl (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hIdxLt))
  have hFr16' : StepFrameSWC (stepRegsAt R (T + 16)) (stepRegsAt R (T + 1)) := hFr16
  have hLeafWork : (stepRegsAt R (T + 1)).work =
      poseidon2Compress12FF (stepAuxLane R T 0) pub.1.pkSeed
        ⟨domainForsLeaf, ‹(kpN <<< 24) ||| ((j <<< 8) ||| stepForsIdxN R T)›,
         ‹tree % 2 ^ 32›, ‹(tree / 2 ^ 32) % 2 ^ 32›⟩ := by
    have hTw : (‹kpN› *ₚ ‹2 ^ 24›) +ₚ (‹j * 2 ^ 8› +ₚ ‹stepForsIdxN R T›) =
        ‹(kpN <<< 24) ||| ((j <<< 8) ||| stepForsIdxN R T)› := by
      have h8 : stepForsIdxN R T < 2 ^ 8 := hIdxLt
      have h1 : j <<< 8 ||| stepForsIdxN R T = j <<< 8 + stepForsIdxN R T :=
        (Nat.shiftLeft_add_eq_or_of_lt h8 j).symm
      have hb : j <<< 8 + stepForsIdxN R T < 2 ^ 24 := by
        rw [Nat.shiftLeft_eq]
        omega
      have h2 : kpN <<< 24 ||| (j <<< 8 + stepForsIdxN R T) =
          kpN <<< 24 + (j <<< 8 + stepForsIdxN R T) :=
        (Nat.shiftLeft_add_eq_or_of_lt hb kpN).symm
      rw [h1, h2, Nat.shiftLeft_eq, Nat.shiftLeft_eq, ← g_ofNat_mul, ← g_ofNat_add,
        ← g_ofNat_add]
    rw [hRL']
    show stepFfAt R T (stepAuxLane R T 0) = _
    simp only [poseidon2Compress12FF.public_eqs, poseidon2CompressWeighted_eq, stepFfAt.public_eqs, stepPermAt]
    rw [hInL, hAddr.kp, hAddr.lo, hAddr.hi, hIdxEq, hTw]
  rw [hLeafWork] at hWalk
  rw [hIdxEq] at hGet
  have hOut : (stepRegsAt R (T + 17)).rem = (stepRegsAt R (T + 16)).rem ∧
      (stepRegsAt R (T + 17)).kp = (stepRegsAt R (T + 16)).kp ∧
      (stepRegsAt R (T + 17)).treeLo = (stepRegsAt R (T + 16)).treeLo ∧
      (stepRegsAt R (T + 17)).treeHi = (stepRegsAt R (T + 16)).treeHi ∧
      (stepRegsAt R (T + 17)).main = (stepRegsAt R (T + 16)).main ∧
      (odd = false → (stepRegsAt R (T + 17)).curRoot = (stepPermAt R (T + 16)).b0) ∧
      (odd = true → (stepRegsAt R (T + 17)).work = (stepPermAt R (T + 16)).b0 ∧
        (stepRegsAt R (T + 17)).curRoot = (stepRegsAt R (T + 16)).curRoot) := by
    cases odd
    · obtain ⟨_, _, hN⟩ := stepSem_forsMerkleBlockB_even hLast
      have hN' : stepRegsAt R (T + 17) = _ := hN
      rw [hN']
      exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun h => Bool.noConfusion h⟩
    · obtain ⟨_, _, hN⟩ := stepSem_forsMerkleBlockB_odd hLast
      have hN' : stepRegsAt R (T + 17) = _ := hN
      rw [hN']
      exact ⟨rfl, rfl, rfl, rfl, rfl, fun h => Bool.noConfusion h, fun _ => ⟨rfl, rfl⟩⟩
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hOut
  exact
    { idxLt := hIdxLt
      get := hGet
      set := o1.trans (hFr16'.rem.trans rem1)
      root := hWalk
      kp := o2.trans (hFr16'.kp.trans kp1)
      treeLo := o3.trans (hFr16'.treeLo.trans lo1)
      treeHi := o4.trans (hFr16'.treeHi.trans hi1)
      main := o5.trans (hFr16'.main.trans main1)
      outE := o6
      outO := fun h => ⟨(o7 h).1, (o7 h).2.trans (hFr16'.curRoot.trans cur1)⟩ }

/-- One FORS pair: two trees and the absorption of their roots. -/

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
def stepForsPairOps (pair : Nat) : List StepOp :=
  (List.range 2).flatMap (fun sub =>
    [StepOp.forsLeafHash (2 * pair + sub) ((2 * pair + sub) / 6)] ++
    (List.range 8).flatMap (fun lvl =>
      [StepOp.forsMerkleBlockA (2 * pair + sub) lvl,
       StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) (sub == 1)])) ++
  [StepOp.forsRootsPairAbsorb pair]

private theorem stepForsPairOps_fun :
    stepForsPairOps = fun pair =>
  (List.range 2).flatMap (fun sub =>
    [StepOp.forsLeafHash (2 * pair + sub) ((2 * pair + sub) / 6)] ++
    (List.range 8).flatMap (fun lvl =>
      [StepOp.forsMerkleBlockA (2 * pair + sub) lvl,
       StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) (sub == 1)])) ++
  [StepOp.forsRootsPairAbsorb pair] := by rfl

/-- What the 35 rows of FORS pair `pair` starting at row `T` establish. -/
structure StepForsPairFacts (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (kpN tree pair T : Nat) : Prop where
  E : StepForsTreeFacts pub R kpN tree (2 * pair) false T
  O : StepForsTreeFacts pub R kpN tree (2 * pair + 1) true (T + 17)
  rem : (stepRegsAt R (T + 35)).rem = (stepRegsAt R (T + 34)).rem
  zero : (pair + 1 == 16) = true → ∀ s < 6, (stepRegsAt R (T + 34)).rem.get s = Goldilocks.zero
  main : (stepRegsAt R (T + 35)).main =
    poseidon2Perm12
      ⟨lane4Add (stepRegsAt R T).main.b0 (stepPermAt R (T + 16)).b0,
       lane4Add (stepRegsAt R T).main.b1 (stepPermAt R (T + 33)).b0,
       (stepRegsAt R T).main.b2⟩
  kp : (stepRegsAt R (T + 35)).kp = (stepRegsAt R T).kp
  treeLo : (stepRegsAt R (T + 35)).treeLo = (stepRegsAt R T).treeLo
  treeHi : (stepRegsAt R (T + 35)).treeHi = (stepRegsAt R T).treeHi

theorem stepForsPair_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {pair kpN tree T : Nat}
    (hRun : StepRunAt pub R (stepForsPairOps pair) T)
    (hAddr : StepAddrOk (stepRegsAt R T) kpN tree) (hk : kpN < 16) (hp : pair < 16) :
    StepForsPairFacts pub R kpN tree pair T := by
  have hTrees : StepRunAt pub R ((List.range 2).flatMap (fun sub =>
      [StepOp.forsLeafHash (2 * pair + sub) ((2 * pair + sub) / 6)] ++
      (List.range 8).flatMap (fun lvl =>
        [StepOp.forsMerkleBlockA (2 * pair + sub) lvl,
         StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) (sub == 1)]))) T := hRun.append_left
  have hTree := StepRunAt.flatMap_range (L := 17) (fun _ => rfl) 2 hTrees
  have hE : StepRunAt pub R (stepForsTreeOps (2 * pair) false) T := hTree 0 (by decide)
  have hO : StepRunAt pub R (stepForsTreeOps (2 * pair + 1) true) (T + 17) :=
    hTree 1 (by decide)
  have hAbs : StepRowSem pub R (.forsRootsPairAbsorb pair) (T + 34) := hRun.get 34 _ rfl
  have E := stepForsTree_sem hE hAddr hk (by omega)
  have hAddr17 : StepAddrOk (stepRegsAt R (T + 17)) kpN tree :=
    ⟨E.kp.trans hAddr.kp, E.treeLo.trans hAddr.lo, E.treeHi.trans hAddr.hi⟩
  have O := stepForsTree_sem hO hAddr17 hk (by omega)
  obtain ⟨hZ, hInA, hRA⟩ := stepSem_forsRootsPairAbsorb hAbs
  have hRA' : stepRegsAt R (T + 35) = _ := hRA
  have m34 : (stepRegsAt R (T + 34)).main = (stepRegsAt R T).main := O.main.trans E.main
  have c34 : (stepRegsAt R (T + 34)).curRoot = (stepPermAt R (T + 16)).b0 :=
    (O.outO rfl).2.trans (E.outE rfl)
  have w34 : (stepRegsAt R (T + 34)).work = (stepPermAt R (T + 33)).b0 := (O.outO rfl).1
  have k34 : (stepRegsAt R (T + 34)).kp = (stepRegsAt R T).kp := O.kp.trans E.kp
  have lo34 : (stepRegsAt R (T + 34)).treeLo = (stepRegsAt R T).treeLo :=
    O.treeLo.trans E.treeLo
  have hi34 : (stepRegsAt R (T + 34)).treeHi = (stepRegsAt R T).treeHi :=
    O.treeHi.trans E.treeHi
  refine
    { E := E, O := O, rem := by rw [hRA'], zero := hZ, main := ?_, kp := ?_, treeLo := ?_,
      treeHi := ?_ }
  · rw [hRA']
    show poseidon2Perm12 (R (T + 34)).stIn = _
    rw [hInA, m34, c34, w34]
  · rw [hRA']; exact k34
  · rw [hRA']; exact lo34
  · rw [hRA']; exact hi34

/-- Row of the `ForsLeafHash` of tree `j` when the `ForsRootsSpongeInit` row is `t0`. -/
def stepForsRow (t0 j : Nat) : Nat := t0 + 1 + 35 * (j / 2) + 17 * (j % 2)

/-- Root of FORS tree `j` as computed by its rows. -/
def stepForsRoot (R : Nat → StepOpRow) (t0 j : Nat) : Lane4 :=
  (stepPermAt R (stepForsRow t0 j + 16)).b0

/-- A FORS opening whose authentication path walks to `rt` is accepted with root `rt`. -/
theorem verifySingleForsOpening_intro (geom : AggSigGeometry) (pkSeed : Digest4)
    (leaf j idx : Nat) (secret : Digest4) (path : List Digest4) (rt : Digest4)
    (hIdx : idx < 2 ^ geom.forsHeight) (hLen : path.length = geom.forsHeight)
    (hWalk : merkleWalkRoot domainForsNode pkSeed 0 (forsHyperTreeIdx geom leaf)
      (forsTreeNodeAddr geom leaf j) 1 idx (forsLeafHash geom pkSeed secret leaf j idx) path =
      rt) :
    verifySingleForsOpening geom pkSeed leaf j idx ⟨secret, path⟩ = some rt := by
  simp only [verifySingleForsOpening.public_eqs]
  simp only [hIdx, hLen, decide_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  exact congrArg some hWalk

/-- **FORS rows.** The 562 rows `ForsRootsSpongeInit .. ForsRootsFinalSqueeze` verify 32 FORS
    openings read from the auxiliary columns, unpack exactly the packed indices, and leave in
    `ST_CUR_ROOT` the sponge of the 32 recovered roots. -/
theorem stepFors_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow} {t0 leaf : Nat}
    (hInit : StepRowSem pub R .forsRootsSpongeInit t0)
    (hPairs : StepRunAt pub R ((List.range 16).flatMap stepForsPairOps) (t0 + 1))
    (hSq : StepRowSem pub R .forsRootsFinalSqueeze (t0 + 561))
    (hAddr : StepAddrOk (stepRegsAt R t0) (leaf % 16) (leaf / 16)) :
    (∀ j < 32, stepForsIdxN R (stepForsRow t0 j) < 256) ∧
    (∀ s a len : Nat, (∀ c < 32, c / 6 = s ↔ a ≤ c ∧ c < a + len) → s < 6 → a + len ≤ 32 →
      256 ^ len < goldilocksPrime →
      ((stepRegsAt R t0).rem.get s).val =
        evalBaseDigits 256
          ((List.range' a len).map (fun c => stepForsIdxN R (stepForsRow t0 c)))) ∧
    (∀ j < 32, verifySingleForsOpening corduroyPoseidon2Geom pub.1.pkSeed leaf j
        (stepForsIdxN R (stepForsRow t0 j)) (stepForsOpening R (stepForsRow t0 j)) =
      some (stepForsRoot R t0 j)) ∧
    (stepRegsAt R (t0 + 562)).curRoot =
      compressForsRootsSponge corduroyPoseidon2Geom pub.1.pkSeed leaf
        ((List.range 32).map (stepForsRoot R t0)) ∧
    StepAddrOk (stepRegsAt R (t0 + 562)) (leaf % 16) (leaf / 16) := by
  have hk : leaf % 16 < 16 := Nat.mod_lt _ (by decide)
  have hPair : ∀ p < 16, StepRunAt pub R (stepForsPairOps p) (t0 + 1 + p * 35) :=
    StepRunAt.flatMap_range (L := 35) (fun _ => rfl) 16 hPairs
  obtain ⟨hInInit, hR1⟩ := stepSem_forsRootsSpongeInit hInit
  have hFrame : ∀ p, p ≤ 16 →
      (stepRegsAt R (t0 + 1 + p * 35)).kp = (stepRegsAt R t0).kp ∧
      (stepRegsAt R (t0 + 1 + p * 35)).treeLo = (stepRegsAt R t0).treeLo ∧
      (stepRegsAt R (t0 + 1 + p * 35)).treeHi = (stepRegsAt R t0).treeHi := by
    intro p
    induction p with
    | zero =>
      intro _
      have h0 : stepRegsAt R (t0 + 1 + 0 * 35) = _ := hR1
      rw [h0]
      exact ⟨rfl, rfl, rfl⟩
    | succ p ih =>
      intro hp
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      have hA : StepAddrOk (stepRegsAt R (t0 + 1 + p * 35)) (leaf % 16) (leaf / 16) :=
        ⟨i1.trans hAddr.kp, i2.trans hAddr.lo, i3.trans hAddr.hi⟩
      have F := stepForsPair_sem (hPair p (by omega)) hA hk (by omega)
      have e : t0 + 1 + (p + 1) * 35 = t0 + 1 + p * 35 + 35 := by omega
      rw [e]
      exact ⟨F.kp.trans i1, F.treeLo.trans i2, F.treeHi.trans i3⟩
  have hF : ∀ p, p < 16 →
      StepForsPairFacts pub R (leaf % 16) (leaf / 16) p (t0 + 1 + p * 35) := by
    intro p hp
    obtain ⟨i1, i2, i3⟩ := hFrame p (by omega)
    exact stepForsPair_sem (hPair p hp)
      ⟨i1.trans hAddr.kp, i2.trans hAddr.lo, i3.trans hAddr.hi⟩ hk hp
  have rowE : ∀ p, stepForsRow t0 (2 * p) = t0 + 1 + p * 35 := by
    intro p; unfold stepForsRow; omega
  have rowO : ∀ p, stepForsRow t0 (2 * p + 1) = t0 + 1 + p * 35 + 17 := by
    intro p; unfold stepForsRow; omega
  have rowN : ∀ p, stepForsRow t0 (2 * p + 1 + 1) = t0 + 1 + p * 35 + 35 := by
    intro p; unfold stepForsRow; omega
  have rootE : ∀ p, stepForsRoot R t0 (2 * p) = (stepPermAt R (t0 + 1 + p * 35 + 16)).b0 := by
    intro p; unfold stepForsRoot; rw [rowE]
  have rootO : ∀ p, stepForsRoot R t0 (2 * p + 1) =
      (stepPermAt R (t0 + 1 + p * 35 + 33)).b0 := by
    intro p; unfold stepForsRoot; rw [rowO]
  have hSplit : ∀ c, c < 32 → ∃ p, p < 16 ∧ (c = 2 * p ∨ c = 2 * p + 1) :=
    fun c hc => ⟨c / 2, by omega, by omega⟩
  have hd : ∀ c < 32, stepForsIdxN R (stepForsRow t0 c) < 256 := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE]; exact (hF p hp).E.idxLt
    · rw [rowO]; exact (hF p hp).O.idxLt
  have hget : ∀ c < 32, ((stepRegsAt R (stepForsRow t0 c)).rem).get (c / 6) =
      ‹stepForsIdxN R (stepForsRow t0 c)› +ₚ (stepAux R (stepForsRow t0 c) 8 *ₚ ‹256›) := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE]; exact (hF p hp).E.get
    · rw [rowO]; exact (hF p hp).O.get
  have hset : ∀ c < 32, (stepRegsAt R (stepForsRow t0 (c + 1))).rem =
      ((stepRegsAt R (stepForsRow t0 c)).rem).set (c / 6)
        (stepAux R (stepForsRow t0 c) 8) := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE, rowO]; exact (hF p hp).E.set
    · rw [rowO, rowN]; exact (hF p hp).rem.trans (hF p hp).O.set
  have hEnd : ∀ s < 6, ((stepRegsAt R (stepForsRow t0 32)).rem).get s = Goldilocks.zero := by
    intro s hs
    have e : stepForsRow t0 32 = t0 + 1 + 15 * 35 + 35 := by unfold stepForsRow; omega
    rw [e, (hF 15 (by decide)).rem]
    exact (hF 15 (by decide)).zero rfl s hs
  have hG0 : (stepRegsAt R (stepForsRow t0 0)).rem = (stepRegsAt R t0).rem := by
    have e : stepForsRow t0 0 = t0 + 1 := by unfold stepForsRow; omega
    rw [e, hR1]
  have hMain : ∀ p, p ≤ 16 → (stepRegsAt R (t0 + 1 + p * 35)).main =
      absorbDigest4Pairs (stepPermAt R t0) ((List.range (2 * p)).map (stepForsRoot R t0)) := by
    intro p
    induction p with
    | zero =>
      intro _
      have h0 : stepRegsAt R (t0 + 1 + 0 * 35) = _ := hR1
      rw [h0]
      simp only [Nat.mul_zero, List.range_zero, List.map_nil,
        absorbDigest4Pairs.public_eqs, absorbPairsPoly.public_eqs]
    | succ p ih =>
      intro hp
      have F := hF p (by omega)
      have e : t0 + 1 + (p + 1) * 35 = t0 + 1 + p * 35 + 35 := by omega
      have e2 : 2 * (p + 1) = 2 * p + 1 + 1 := by omega
      rw [e, F.main, ih (by omega), e2, List.range_succ, List.range_succ, List.append_assoc,
        List.map_append]
      simp only [absorbDigest4Pairs.public_eqs]
      have hEven : ((List.range (2 * p)).map (stepForsRoot R t0)).length % 2 = 0 := by
        rw [List.length_map, List.length_range]
        omega
      have hApp := absorbPairsPoly_append_pair
        (fun (s : Poseidon2State12) (e0 : Lane4) =>
          poseidon2Perm12 ⟨lane4Add s.b0 e0, s.b1, s.b2⟩)
        (fun (s : Poseidon2State12) (e0 e1 : Lane4) =>
          poseidon2Perm12 ⟨lane4Add s.b0 e0, lane4Add s.b1 e1, s.b2⟩)
        (stepPermAt R (t0 + 1 + p * 35 + 16)).b0 (stepPermAt R (t0 + 1 + p * 35 + 33)).b0
        _ (stepPermAt R t0) hEven
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
      rw [rootE, rootO]
      exact hApp.symm
  obtain ⟨hInSq, hR562⟩ := stepSem_forsRootsFinalSqueeze hSq
  have hR562' : stepRegsAt R (t0 + 562) = _ := hR562
  obtain ⟨f1, f2, f3⟩ := hFrame 16 (Nat.le_refl _)
  have e16 : t0 + 1 + 16 * 35 = t0 + 561 := by omega
  rw [e16] at f1 f2 f3
  have hM16 := hMain 16 (Nat.le_refl _)
  rw [e16] at hM16
  refine ⟨hd, ?_, ?_, ?_, ?_⟩
  · intro s a len hRange hs haN hLen
    have h := stepRemSlot_digits
      (fun c => (stepRegsAt R (stepForsRow t0 c)).rem) 256 (by decide)
      (fun c => stepForsIdxN R (stepForsRow t0 c))
      (fun c => stepAux R (stepForsRow t0 c) 8) (fun c => c / 6) 32
      hd hget hset (fun c hc => by show c / 6 < 6; omega) s a len hRange haN (hEnd s hs) hLen
    rw [← hG0]
    exact h
  · intro j hj
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit j hj
    · rw [rootE, rowE]
      exact verifySingleForsOpening_intro corduroyPoseidon2Geom _ leaf (2 * p) _ _ _ _
        (by simpa only [corduroyPoseidon2Geom.public_eqs] using (hF p hp).E.idxLt)
        (by simp only [List.length_map, List.length_range, corduroyPoseidon2Geom.public_eqs]) (by simpa only [forsLeafHash.public_eqs, forsLeafAddr.public_eqs, forsLeafTweak4.public_eqs,
          forsKpIdx.public_eqs, forsHyperTreeIdx.public_eqs,
          forsTreeNodeAddr.public_eqs, corduroyPoseidon2Geom.public_eqs,
          Nat.add_assoc, Nat.reduceAdd] using (hF p hp).E.root)
    · rw [rootO, rowO]
      exact verifySingleForsOpening_intro corduroyPoseidon2Geom _ leaf (2 * p + 1) _ _ _ _
        (by simpa only [corduroyPoseidon2Geom.public_eqs] using (hF p hp).O.idxLt)
        (by simp only [List.length_map, List.length_range, corduroyPoseidon2Geom.public_eqs]) (by simpa only [forsLeafHash.public_eqs, forsLeafAddr.public_eqs, forsLeafTweak4.public_eqs,
          forsKpIdx.public_eqs, forsHyperTreeIdx.public_eqs,
          forsTreeNodeAddr.public_eqs, corduroyPoseidon2Geom.public_eqs,
          Nat.add_assoc, Nat.reduceAdd] using (hF p hp).O.root)
  · have hInit' : (R t0).stIn =
        ⟨pub.1.pkSeed,
         ⟨‹leaf % 16›, ‹(leaf / 16) % 2 ^ 32›, ‹(leaf / 16 / 2 ^ 32) % 2 ^ 32›, ‹32›⟩,
         ⟨domainForsRoots, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩ := by
      rw [hInInit, hAddr.kp, hAddr.lo, hAddr.hi]
    rw [hR562']
    show (stepPermAt R (t0 + 561)).b0 = _
    unfold stepPermAt
    rw [hInSq]
    unfold stepSqueezeIn
    rw [hM16]
    simp only [stepPermAt, compressForsRootsSponge.public_eqs]
    rw [hInit', (corduroy_fors_addr_split leaf).1, (corduroy_fors_addr_split leaf).2]
    simp only [corduroyPoseidon2Geom.public_eqs]
  · rw [hR562']
    exact ⟨f1.trans hAddr.kp, f2.trans hAddr.lo, f3.trans hAddr.hi⟩

/-! ### §3.17. Hypertree layers of the stateless profile -/

/-- The 465 rows of one hypertree layer of the stateless profile. -/
def stepCordLayerOps (layer : Nat) (isTop : Bool) : List StepOp :=
  [StepOp.detTreeHmsgBlock0 layer, StepOp.detTreeHmsgBlock1 layer] ++
    (List.range 5).map StepOp.hmsgDecompLimb ++ pushLayerWotsAndMerkle layer 4 isTop

private theorem stepCordLayerOps_last (layer : Nat) (isTop : Bool) :
    (stepCordLayerOps layer isTop)[464]? = some (.xmssMerkleBlockB true isTop) := by
  simp only [stepCordLayerOps, List.getElem?_append, List.length_append,
    List.length_cons, List.length_nil, List.length_map, List.length_range,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
    pushLayerWotsAndMerkle_four_last]

/-- The WOTS+C counter read from the 32 bits of a `DetTreeHmsgBlock1` row; `tL` is the row of
    the layer's `DetTreeHmsgBlock0`. -/
def stepCordCtr (R : Nat → StepOpRow) (tL : Nat) : Nat :=
  stepWeightedNat (stepAux R (tL + 1)) (fun i => 2 ^ i) 32

/-- The layer signature read from the rows of a layer starting at row `tL`. -/
def stepCordLayerSig (R : Nat → StepOpRow) (tL : Nat) : WotsLayerSig :=
  ⟨stepCordCtr R tL, stepLayerChains R (tL + 7), stepLayerPath R (tL + 457) 4⟩

/-- **Stateless layer rows.** The 465 rows of a layer hash the child root in `ST_CUR_ROOT`
    under the deterministic tree `H_msg`, verify one WOTS+C layer against it, and either pin
    the walked root to the public key (top layer) or move it to `ST_CUR_ROOT` and shift the
    tree index by the subtree height (inner layers). -/
theorem stepCordLayer_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer tL kpN tree : Nat} {isTop : Bool}
    (hRun : StepRunAt pub R (stepCordLayerOps layer isTop) tL)
    (hAddr : StepAddrOk (stepRegsAt R tL) kpN tree) (hl : layer < 16) (hk : kpN < 16) :
    verifyWotsLayer corduroyPoseidon2Geom pub.1 layer tree kpN
        (computeHmsgDetTree pub.1 layer tree kpN (stepCordLayerSig R tL).tswCtr
          (stepRegsAt R tL).curRoot)
        (stepCordLayerSig R tL) =
      some (stepPermAt R (tL + 464)).b0 ∧
    (isTop = true → (stepPermAt R (tL + 464)).b0 = pub.1.pkRoot) ∧
    (isTop = false → tree < 2 ^ 64 →
      StepAddrOk (stepRegsAt R (tL + 465)) (tree % 16) (tree / 16) ∧
      (stepRegsAt R (tL + 465)).curRoot = (stepPermAt R (tL + 464)).b0) := by
  have b0 : StepRowSem pub R (.detTreeHmsgBlock0 layer) tL := hRun.get 0 _ rfl
  have b1 : StepRowSem pub R (.detTreeHmsgBlock1 layer) (tL + 1) := hRun.get 1 _ rfl
  have hDec : StepRunAt pub R ((List.range 5).map StepOp.hmsgDecompLimb) (tL + 2) :=
    hRun.append_left.append_right
  have hLayer : StepRunAt pub R (pushLayerWotsAndMerkle layer 4 isTop) (tL + 2 + 5) :=
    hRun.append_right
  have hLast : StepRowSem pub R (.xmssMerkleBlockB true isTop) (tL + 464) :=
    hRun.get 464 _ (stepCordLayerOps_last layer isTop)
  obtain ⟨hIn0, hR1⟩ := stepSem_detTreeHmsgBlock0 b0
  obtain ⟨hBits, hIn1, hR2⟩ := stepSem_detTreeHmsgBlock1 b1
  have hR1' : stepRegsAt R (tL + 1) = _ := hR1
  have hR2' : stepRegsAt R (tL + 2) = _ := hR2
  have hCtr : stepCordCtr R tL < 2 ^ 32 := stepWeightedNat_bits_lt (stepAux R (tL + 1)) 32 hBits
  have hRem0 : ∀ s < 6, (stepRegsAt R (tL + 2)).rem.get s = Goldilocks.zero := by
    intro s hs
    rw [hR2']
    rcases s with _ | _ | _ | _ | _ | _ | s
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hs (by omega)
  have hAcc0 : (stepRegsAt R (tL + 2)).acc = Goldilocks.zero := by rw [hR2']
  have hAddr2 : StepAddrOk (stepRegsAt R (tL + 2)) kpN tree := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hR2', hR1']; exact hAddr.kp
    · rw [hR2', hR1']; exact hAddr.lo
    · rw [hR2', hR1']; exact hAddr.hi
  have hHm : stepHmsgOf (stepRegsAt R (tL + 2)).main =
      computeHmsgDetTree pub.1 layer tree kpN (stepCordCtr R tL) (stepRegsAt R tL).curRoot := by
    have hM1 : (stepRegsAt R (tL + 1)).main = poseidon2Perm12 (R tL).stIn := by rw [hR1']; rfl
    have hM2 : (stepRegsAt R (tL + 2)).main = poseidon2Perm12 (R (tL + 1)).stIn := by
      rw [hR2']; rfl
    have hC1 : (stepRegsAt R (tL + 1)).curRoot = (stepRegsAt R tL).curRoot := by rw [hR1']
    have hLK : (‹layer * 2 ^ 32› : Goldilocks) +ₚ ‹kpN› =
        ‹(layer % 2 ^ 32) * 2 ^ 32 + kpN % 2 ^ 32› := by
      rw [← g_ofNat_add, Nat.mod_eq_of_lt (by omega : layer < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : kpN < 2 ^ 32)]
    have hCt : stepWeightedSum (stepAux R (tL + 1)) (fun i => 2 ^ i) 32 =
        ‹stepCordCtr R tL % 2 ^ 32› := by
      rw [stepWeightedSum_eq_ofNat, Nat.mod_eq_of_lt hCtr]
      rfl
    rw [hM2, hIn1, hM1, hC1, hIn0, hAddr.kp, hAddr.lo, hAddr.hi, hLK, hCt]
    simp only [stepHmsgOf, computeHmsgDetTree.public_eqs]
  have hLastFacts : (R (tL + 464)).stIn = stepMerkleBIn (stepRegsAt R (tL + 464)) ∧
      (stepRegsAt R (tL + 464)).cursor = Goldilocks.zero := by
    cases isTop
    · obtain ⟨a, b, _⟩ := stepSem_xmssMerkleBlockB_link hLast
      exact ⟨a, b⟩
    · obtain ⟨a, b, _⟩ := stepSem_xmssMerkleBlockB_top hLast
      exact ⟨a, b⟩
  obtain ⟨_, hV, _, hAddr464⟩ := stepLayer_verify (geom := corduroyPoseidon2Geom)
    (layer := layer) (h := 4) (tD := tL + 2) (ctr := stepCordCtr R tL) hDec hLayer hRem0 hAcc0
    hAddr2 hLastFacts.1 hLastFacts.2 (by omega) (by omega) (by decide) (by decide)
    (by simp only [corduroyPoseidon2Geom.public_eqs])
    (by simp only [corduroyPoseidon2Geom.public_eqs])
    (by simp only [corduroyPoseidon2Geom.public_eqs])
  have hAddr464' : StepAddrOk (stepRegsAt R (tL + 464)) kpN tree := hAddr464
  rw [hHm] at hV
  refine ⟨hV, ?_, ?_⟩
  · intro hT
    subst hT
    exact (stepSem_xmssMerkleBlockB_top hLast).2.2
  · intro hT hTree
    subst hT
    obtain ⟨_, _, hB4, hQa, hQ2, hQb, hLo, hHi, hRn⟩ := stepSem_xmssMerkleBlockB_link hLast
    have hRn' : stepRegsAt R (tL + 465) = _ := hRn
    have nb : stepWeightedNat (stepAux R (tL + 464)) (fun i => 2 ^ i) 4 < 2 ^ 4 :=
      stepWeightedNat_bits_lt _ 4 hB4
    have nA : stepWeightedNat (fun i => stepAux R (tL + 464) (4 + i)) (fun i => 4 ^ i) 14 <
        4 ^ 14 := stepWeightedNat_lt 4 _ 14 hQa
    have n2 : stepWeightedNat (fun i => stepAux R (tL + 464) (18 + i)) (fun i => 4 ^ i) 2 <
        4 ^ 2 := stepWeightedNat_lt 4 _ 2 hQ2
    have nB : stepWeightedNat (fun i => stepAux R (tL + 464) (20 + i)) (fun i => 4 ^ i) 14 <
        4 ^ 14 := stepWeightedNat_lt 4 _ 14 hQb
    rw [stepWeightedSum_eq_ofNat, stepWeightedSum_eq_ofNat, ← g_ofNat_mul, ← g_ofNat_add,
      hAddr464'.lo] at hLo
    rw [stepWeightedSum_eq_ofNat, stepWeightedSum_eq_ofNat, ← g_ofNat_mul, ← g_ofNat_add,
      hAddr464'.hi] at hHi
    have eLo := g_ofNat_inj (by rw [goldilocksPrime_eq]; omega)
      (by rw [goldilocksPrime_eq]; omega) hLo
    have eHi := g_ofNat_inj (by rw [goldilocksPrime_eq]; omega)
      (by rw [goldilocksPrime_eq]; omega) hHi
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hRn']
      show stepWeightedSum (stepAux R (tL + 464)) (fun i => 2 ^ i) 4 = _
      rw [stepWeightedSum_eq_ofNat]
      exact congrArg Goldilocks.ofNat (by omega)
    · rw [hRn']
      show stepWeightedSum (fun i => stepAux R (tL + 464) (4 + i)) (fun i => 4 ^ i) 14 +ₚ
        (stepWeightedSum (fun i => stepAux R (tL + 464) (18 + i)) (fun i => 4 ^ i) 2 *ₚ
          ‹2 ^ 28›) = _
      rw [stepWeightedSum_eq_ofNat, stepWeightedSum_eq_ofNat, ← g_ofNat_mul, ← g_ofNat_add]
      exact congrArg Goldilocks.ofNat (by omega)
    · rw [hRn']
      show stepWeightedSum (fun i => stepAux R (tL + 464) (20 + i)) (fun i => 4 ^ i) 14 = _
      rw [stepWeightedSum_eq_ofNat]
      exact congrArg Goldilocks.ofNat (by omega)
    · rw [hRn']

/-! ### §3.18. Active `CorduroyPoseidon2` slot: an accepted table yields a native signature -/

private theorem verifyForsPoly_map {OP D : Type} (step : Nat → Nat → OP → Option D)
    (idx : Nat → Nat) (op : Nat → OP) (rt : Nat → D) :
    ∀ (n t0 : Nat), (∀ i, t0 ≤ i → i < t0 + n → step i (idx i) (op i) = some (rt i)) →
      verifyForsPoly step ((List.range' t0 n).map idx) ((List.range' t0 n).map op) t0 =
        some ((List.range' t0 n).map rt)
  | 0, _, _ => by simp only [List.range'_zero, List.map_nil, verifyForsPoly.public_eqs]
  | n + 1, t0, h => by
    have e : List.range' t0 (n + 1) = t0 :: List.range' (t0 + 1) n := rfl
    have ih := verifyForsPoly_map step idx op rt n (t0 + 1)
      (fun i h1 h2 => h i (by omega) (by omega))
    rw [e, List.map_cons, List.map_cons, List.map_cons]
    simp only [verifyForsPoly.public_eqs, h t0 (Nat.le_refl _) (by omega), ih]

/-- Upper layers verify one after another when each layer verifies against the root of the
    layer below and the remaining tree index is shifted by the subtree height. -/
private theorem verifyUpperLayers_chain (geom : AggSigGeometry) (pk : AggValidatorPk)
    (sigL : Nat → WotsLayerSig) (cur : Nat → Digest4) (rem : Nat → Nat) :
    ∀ (n l0 : Nat),
      (∀ l, l0 ≤ l → l < l0 + n →
        verifyWotsLayer geom pk l (rem l / 2 ^ geom.subtreeHeight)
            (rem l % 2 ^ geom.subtreeHeight)
            (computeHmsgDetTree pk l (rem l / 2 ^ geom.subtreeHeight)
              (rem l % 2 ^ geom.subtreeHeight) (sigL l).tswCtr (cur l)) (sigL l) =
          some (cur (l + 1)) ∧
        rem (l + 1) = rem l / 2 ^ geom.subtreeHeight) →
      verifyUpperLayers geom pk l0 (rem l0) (cur l0) ((List.range' l0 n).map sigL) =
        some (cur (l0 + n))
  | 0, _, _ => by simp only [List.range'_zero, List.map_nil,
      verifyUpperLayers.public_eqs, verifyUpperPoly.public_eqs, Nat.add_zero]
  | n + 1, l0, h => by
    have e : List.range' l0 (n + 1) = l0 :: List.range' (l0 + 1) n := rfl
    have hs := h l0 (Nat.le_refl _) (by omega)
    have ih := verifyUpperLayers_chain geom pk sigL cur rem n (l0 + 1)
      (fun l h1 h2 => h l (by omega) (by omega))
    simp only [verifyUpperLayers.public_eqs] at ih ⊢
    rw [e, List.map_cons]
    simp only [verifyUpperPoly.public_eqs, hs.1]
    rw [← hs.2, show l0 + (n + 1) = l0 + 1 + n by omega]
    exact ih

/-- A stateless signature is accepted once the XOF derive, the FORS openings, the bottom
    layer and the upper layers each verify. -/
theorem verifyAggNativeSig_stateless_intro (geom : AggSigGeometry) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (fors : List AggForsTreeOpening)
    (lsig0 : WotsLayerSig) (upper : List WotsLayerSig)
    (leaf : Nat) (idxs : List Nat) (forsPk root0 : Digest4)
    (hWf : geom.wellFormed = true) (hPk : pk.profile = geom.profile)
    (hNL : (lsig0 :: upper).length = geom.numLayers) (hF : (geom.forsTrees == 0) = false)
    (hXof : deriveStatelessLeafAndForsChecked geom pk rRand (computeMessageMu pk msg) =
      some (leaf, idxs))
    (hFors : verifyAndRecoverForsPk geom pk.pkSeed leaf idxs fors = some forsPk)
    (hL0 : verifyWotsLayer geom pk 0 (leaf / 2 ^ geom.subtreeHeight)
        (leaf % 2 ^ geom.subtreeHeight)
        (computeHmsgDetTree pk 0 (leaf / 2 ^ geom.subtreeHeight)
          (leaf % 2 ^ geom.subtreeHeight) lsig0.tswCtr forsPk) lsig0 = some root0)
    (hUp : verifyUpperLayers geom pk 1 (leaf / 2 ^ geom.subtreeHeight) root0 upper =
      some pk.pkRoot) :
    verifyAggNativeSig geom pk msg ⟨geom.profile, rRand, 0, fors, lsig0 :: upper⟩ = true := by
  have hCond : (!geom.wellFormed || pk.profile != geom.profile ||
      geom.profile != geom.profile || ((lsig0 :: upper).length != geom.numLayers)) = false := by
    rw [hWf, hPk, hNL]
    simp
  simp only [verifyAggNativeSig.public_eqs]
  simp only [hCond, Bool.false_eq_true, ↓reduceIte, hF]
  simp only [verifyAggNativeSigStateless.public_eqs]
  exact evalStatelessFlow_ok _ _ _ _ _ leaf idxs forsPk root0 pk.pkRoot hXof hFors hL0 hUp
    (beq_self_eq_true _)

/-- Row of the `DetTreeHmsgBlock0` of hypertree layer `l` in a `CorduroyPoseidon2` block. -/
def stepCordLayerRow (l : Nat) : Nat := 571 + l * 465

/-- The native signature read from the auxiliary columns of a `CorduroyPoseidon2` signer
    block: `rRand` from the `StatelessDeriveBlock1` row, the 32 FORS openings from the
    `ForsLeafHash` and `ForsMerkleBlockA` rows, and per hypertree layer the counter bits of the
    `DetTreeHmsgBlock1` row, the chain values of the `WotsChainStep0` rows and the
    authentication path of the `XmssMerkleBlockA` rows. -/
def stepCordSig (R : Nat → StepOpRow) : AggNativeSignature :=
  { profile := .corduroyPoseidon2
    rRand := stepAuxLane R 1 0
    statefulLeafIdx := 0
    forsOpenings := (List.range' 0 32).map (fun j => stepForsOpening R (stepForsRow 9 j))
    layers := (List.range' 0 16).map (fun l => stepCordLayerSig R (stepCordLayerRow l)) }

theorem stepCordLayerOps_length (layer : Nat) (isTop : Bool) :
    (stepCordLayerOps layer isTop).length = 465 := by
  unfold stepCordLayerOps
  rw [List.length_append, pushLayerWotsAndMerkle_eq, List.length_append, List.length_append,
    stepWotsOps_length]
  rfl

theorem stepForsPairOps_length (pair : Nat) : (stepForsPairOps pair).length = 35 := by
  rfl

/-- **Native-signature witness extraction, `CorduroyPoseidon2` profile.** If the 256-column
    `StepOp` table is accepted and slot `k` is active with public inputs `(pk, mu)`, `mu` the
    message representative of `msg` under `pk`, then the stateless signature read from the
    auxiliary columns of the slot's rows is accepted by the native verifier. -/
theorem stepOp256TableOk_corduroy_extract (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hTable : stepOp256TableOk .corduroyPoseidon2 slots rows = true)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .corduroyPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    verifyAggNativeSig corduroyPoseidon2Geom pub.1 msg
      (stepCordSig (stepOpSlotRow .corduroyPoseidon2 rows k)) = true := by
  obtain ⟨R, hR⟩ : ∃ R, R = stepOpSlotRow .corduroyPoseidon2 rows k := ⟨_, rfl⟩
  rw [← hR]
  have hSH : corduroyPoseidon2Geom.subtreeHeight = 4 := by
    simp only [corduroyPoseidon2Geom.public_eqs]
  have hRun0 := stepOp256TableOk_slot_run .corduroyPoseidon2 slots rows k pub hTable hSlot
  rw [← hR] at hRun0
  have hRun : StepRunAt pub R
      ((((stepDeriveOps ++ [StepOp.forsRootsSpongeInit]) ++
          (List.range 16).flatMap stepForsPairOps) ++ [StepOp.forsRootsFinalSqueeze]) ++
        (List.range 16).flatMap (fun layer => stepCordLayerOps layer (layer + 1 == 16))) 0 := by
    simpa only [signerProgramBody.public_eqs, stepDeriveOps, stepForsPairOps_fun,
      stepCordLayerOps, List.append_assoc] using hRun0
  have hDerive : StepRunAt pub R stepDeriveOps 0 :=
    hRun.append_left.append_left.append_left.append_left
  have hI : StepRowSem pub R .forsRootsSpongeInit 9 :=
    hRun.append_left.append_left.append_left.append_right.head
  have hPairs : StepRunAt pub R ((List.range 16).flatMap stepForsPairOps) (9 + 1) :=
    hRun.append_left.append_left.append_right
  have hlenPre : ((stepDeriveOps ++ [StepOp.forsRootsSpongeInit]) ++
      (List.range 16).flatMap stepForsPairOps).length = 570 := by
    rw [List.length_append, flatMap_range_uniform_length _ 35 stepForsPairOps_length]
    rfl
  have hSq : StepRowSem pub R .forsRootsFinalSqueeze (9 + 561) := by
    have h := hRun.append_left.append_right
    rw [hlenPre] at h
    exact h.head
  have hLayers : StepRunAt pub R
      ((List.range 16).flatMap (fun layer => stepCordLayerOps layer (layer + 1 == 16))) 571 := by
    have h := hRun.append_right
    rw [List.length_append, hlenPre] at h
    exact h
  have hL : ∀ l < 16, StepRunAt pub R (stepCordLayerOps l (l + 1 == 16)) (571 + l * 465) :=
    StepRunAt.flatMap_range (L := 465) (fun l => stepCordLayerOps_length l _) 16 hLayers
  obtain ⟨hLimbs, hPack, hAddr9⟩ := stepStatelessDerive_sem hDerive
  obtain ⟨m, hm⟩ : ∃ m, m = stepXofState pub R := ⟨_, rfl⟩
  obtain ⟨leaf, hleaf⟩ : ∃ leaf, leaf = stepXofLeaf m := ⟨_, rfl⟩
  rw [← hm] at hLimbs hPack hAddr9
  rw [← hleaf] at hAddr9
  obtain ⟨hIdxLt, hSlots, hRoots, hCur571, hAddr571⟩ :=
    stepFors_sem (t0 := 9) (leaf := leaf) hI hPairs hSq hAddr9
  have hCur571' : (stepRegsAt R 571).curRoot = _ := hCur571
  have hAddr571' : StepAddrOk (stepRegsAt R 571) (leaf % 16) (leaf / 16) := hAddr571
  -- The indices the rows open are the indices the XOF derives.
  have hIdxSlot : ∀ s a len : Nat, (∀ c < 32, c / 6 = s ↔ a ≤ c ∧ c < a + len) → s < 6 →
      a + len ≤ 32 → len ≤ 6 → 6 * s = a → ∀ c, a ≤ c → c < a + len →
      stepForsIdxN R (stepForsRow 9 c) = stepForsIdx m c := by
    intro s a len hRange hs haN hLen6 hStart c hac hcl
    have hLen : 256 ^ len < goldilocksPrime :=
      Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hLen6) (by decide)
    have h1 := hSlots s a len hRange hs haN hLen
    have h2 := hPack s hs
    rw [stepPackFoldG_slot 256 _ _ _ 32 s a len hRange haN hStart] at h2
    have hLtB : evalBaseDigits 256 ((List.range' a len).map (stepForsIdx m)) < 256 ^ len := by
      have h := evalBaseDigits_lt_pow 256 (by decide) ((List.range' a len).map (stepForsIdx m))
        (fun d hd => by
          obtain ⟨c', _, rfl⟩ := List.mem_map.mp hd
          exact stepForsIdx_lt m c')
      rw [List.length_map, List.length_range'] at h
      exact h
    rw [h2, Goldilocks.ofNat_val, Nat.mod_eq_of_lt (Nat.lt_trans hLtB hLen)] at h1
    have hEq := evalBaseDigits_inj 256 (by decide)
      (by rw [List.length_map, List.length_map])
      (fun d hd => by
        obtain ⟨c', _, rfl⟩ := List.mem_map.mp hd
        exact stepForsIdx_lt m c')
      (fun d hd => by
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hd
        have hb := mem_range'_bounds _ _ _ hc'
        exact hIdxLt c' (by omega))
      h1
    exact (List.map_inj_left.mp hEq c (mem_range'_of_bounds len a c hac hcl)).symm
  have hIdx : ∀ j < 32, stepForsIdxN R (stepForsRow 9 j) = stepForsIdx m j := by
    intro j hj
    by_cases h5 : j / 6 < 5
    · exact hIdxSlot (j / 6) (6 * (j / 6)) 6 (fun c hc => ⟨fun h => ⟨by omega, by omega⟩, fun h => by omega⟩) (by omega) (by omega)
        (Nat.le_refl _) rfl j (by omega) (by omega)
    · exact hIdxSlot (j / 6) (6 * (j / 6)) 2 (fun c hc => ⟨fun h => ⟨by omega, by omega⟩, fun h => by omega⟩) (by omega) (by omega)
        (by decide) rfl j (by omega) (by omega)
  -- The stateless XOF derive of the native verifier.
  have hLeafLt : leaf < 2 ^ 64 := by rw [hleaf]; unfold stepXofLeaf; omega
  have hXof : deriveStatelessLeafAndForsChecked corduroyPoseidon2Geom pub.1 (stepAuxLane R 1 0)
      pub.2 = some (leaf, (List.range' 0 32).map (stepForsIdx m)) := by
    have hAll : ([m.b0.x0, m.b0.x1, m.b0.x2, m.b0.x3, m.b1.x0, m.b1.x1, m.b1.x2].all
        (fun l => decide (l.val < 2 ^ 63))) = true := by
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨hLimbs 0 (by decide), hLimbs 1 (by decide), hLimbs 2 (by decide),
        hLimbs 3 (by decide), hLimbs 4 (by decide), hLimbs 5 (by decide),
        hLimbs 6 (by decide)⟩
    have hIdxL : (List.range 32).map (fun t =>
        (statelessForsSourceLimb m (t / 7) / (256 ^ (t % 7))) % 2 ^ 8) =
        (List.range' 0 32).map (stepForsIdx m) := by
      rw [← List.range_eq_range']
      apply List.map_congr_left
      intro t ht
      have ht' := List.mem_range.mp ht
      have h7 : t / 7 = 0 ∨ t / 7 = 1 ∨ t / 7 = 2 ∨ t / 7 = 3 ∨ t / 7 = 4 := by omega
      unfold stepForsIdx
      rcases h7 with h | h | h | h | h <;> rw [h] <;>
        (simp only [statelessForsSourceLimb.public_eqs]; rfl)
    have key : deriveStatelessLeafAndForsChecked corduroyPoseidon2Geom pub.1 (stepAuxLane R 1 0)
        pub.2 =
        (if ([m.b0.x0, m.b0.x1, m.b0.x2, m.b0.x3, m.b1.x0, m.b1.x1, m.b1.x2].all
            (fun l => decide (l.val < 2 ^ 63))) = true then
          some (stepXofLeaf m % 2 ^ 64, (List.range 32).map (fun t =>
            (statelessForsSourceLimb m (t / 7) / (256 ^ (t % 7))) % 2 ^ 8))
        else none) := by
      rw [hm]
      simp only [deriveStatelessLeafAndForsChecked.public_eqs, stepXofState,
        stepXofLeaf, corduroyPoseidon2Geom.public_eqs, Nat.reduceMul, Nat.reducePow]
      rfl
    rw [key, hIdxL, hAll, ← hleaf, Nat.mod_eq_of_lt hLeafLt]
    rfl
  -- The FORS public key.
  have hFors : verifyAndRecoverForsPk corduroyPoseidon2Geom pub.1.pkSeed leaf
      ((List.range' 0 32).map (stepForsIdx m))
      ((List.range' 0 32).map (fun j => stepForsOpening R (stepForsRow 9 j))) =
      some (stepRegsAt R 571).curRoot := by
    have hAux : verifyForsTreesAux corduroyPoseidon2Geom pub.1.pkSeed leaf 0
        ((List.range' 0 32).map (stepForsIdx m))
        ((List.range' 0 32).map (fun j => stepForsOpening R (stepForsRow 9 j))) =
        some ((List.range' 0 32).map (stepForsRoot R 9)) := by
      simp only [verifyForsTreesAux.public_eqs]
      exact verifyForsPoly_map _ _ _ _ 32 0 (fun i _ hi => by
        have h := hRoots i (by omega)
        rw [hIdx i (by omega)] at h
        exact h)
    simp only [verifyAndRecoverForsPk.public_eqs]
    simp only [List.length_map, List.length_range', hAux]
    rw [hCur571', List.range_eq_range']
    simp only [show corduroyPoseidon2Geom.forsTrees = 32 by simp only [corduroyPoseidon2Geom.public_eqs],
      beq_self_eq_true, Bool.and_self, ↓reduceIte]
  -- The hypertree layers.
  have hInv : ∀ l, l < 16 →
      StepAddrOk (stepRegsAt R (571 + l * 465)) ((leaf / 16 ^ l) % 16) (leaf / 16 ^ (l + 1)) := by
    intro l
    induction l with
    | zero =>
      intro _
      have e : 571 + 0 * 465 = 571 := by omega
      rw [e, Nat.pow_zero, Nat.div_one, Nat.pow_one]
      exact hAddr571'
    | succ l ih =>
      intro hl
      have hA := ih (by omega)
      have hRunL := hL l (by omega)
      rw [beq_false_of_ne (by omega : l + 1 ≠ 16)] at hRunL
      obtain ⟨_, _, hLink⟩ := stepCordLayer_sem hRunL hA (by omega)
        (Nat.mod_lt _ (by decide))
      obtain ⟨hA', _⟩ := hLink rfl
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLeafLt)
      have e : 571 + (l + 1) * 465 = 571 + l * 465 + 465 := by omega
      have e2 : leaf / 16 ^ (l + 1 + 1) = leaf / 16 ^ (l + 1) / 16 := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      rw [e, e2]
      exact hA'
  obtain ⟨cur, hcur⟩ : ∃ cur : Nat → Digest4, cur = fun l => match l with
      | 0 => (stepRegsAt R 571).curRoot
      | l + 1 => (stepPermAt R (571 + l * 465 + 464)).b0 := ⟨_, rfl⟩
  have hCurRow : ∀ l, l < 16 → (stepRegsAt R (571 + l * 465)).curRoot = cur l := by
    intro l hl
    rcases l with _ | l
    · rw [hcur]
    · have hRunL := hL l (by omega)
      rw [beq_false_of_ne (by omega : l + 1 ≠ 16)] at hRunL
      obtain ⟨_, _, hLink⟩ := stepCordLayer_sem hRunL (hInv l (by omega)) (by omega)
        (Nat.mod_lt _ (by decide))
      obtain ⟨_, hC⟩ := hLink rfl
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLeafLt)
      have e : 571 + (l + 1) * 465 = 571 + l * 465 + 465 := by omega
      rw [e, hC, hcur]
  have hLayerV : ∀ l, l < 16 →
      verifyWotsLayer corduroyPoseidon2Geom pub.1 l
          (leaf / 16 ^ l / 2 ^ corduroyPoseidon2Geom.subtreeHeight)
          (leaf / 16 ^ l % 2 ^ corduroyPoseidon2Geom.subtreeHeight)
          (computeHmsgDetTree pub.1 l (leaf / 16 ^ l / 2 ^ corduroyPoseidon2Geom.subtreeHeight)
            (leaf / 16 ^ l % 2 ^ corduroyPoseidon2Geom.subtreeHeight)
            (stepCordLayerSig R (stepCordLayerRow l)).tswCtr (cur l))
          (stepCordLayerSig R (stepCordLayerRow l)) = some (cur (l + 1)) := by
    intro l hl
    obtain ⟨hV, _, _⟩ := stepCordLayer_sem (hL l hl) (hInv l hl) hl (Nat.mod_lt _ (by decide))
    have e2 : leaf / 16 ^ l / 2 ^ corduroyPoseidon2Geom.subtreeHeight = leaf / 16 ^ (l + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      simp only [hSH, Nat.reducePow]
    have e3 : leaf / 16 ^ l % 2 ^ corduroyPoseidon2Geom.subtreeHeight = leaf / 16 ^ l % 16 := by simp only [hSH, Nat.reducePow]
    rw [e2, e3, ← hCurRow l hl]
    have e4 : cur (l + 1) = (stepPermAt R (571 + l * 465 + 464)).b0 := by rw [hcur]
    rw [e4]
    exact hV
  have hTop : cur 16 = pub.1.pkRoot := by
    obtain ⟨_, hT, _⟩ := stepCordLayer_sem (hL 15 (by decide)) (hInv 15 (by decide))
      (by decide) (Nat.mod_lt _ (by decide))
    rw [hcur]
    exact hT rfl
  have hUp := verifyUpperLayers_chain corduroyPoseidon2Geom pub.1
    (fun l => stepCordLayerSig R (stepCordLayerRow l)) cur (fun l => leaf / 16 ^ l) 15 1
    (fun l _ h2 => ⟨hLayerV l (by omega), by
      show leaf / 16 ^ (l + 1) = leaf / 16 ^ l / 2 ^ corduroyPoseidon2Geom.subtreeHeight
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      simp only [hSH, Nat.reducePow]⟩)
  have hL0 := hLayerV 0 (by decide)
  rw [Nat.pow_zero, Nat.div_one] at hL0
  have hUp' : verifyUpperLayers corduroyPoseidon2Geom pub.1 1
      (leaf / 2 ^ corduroyPoseidon2Geom.subtreeHeight) (cur 1)
      ((List.range' 1 15).map (fun l => stepCordLayerSig R (stepCordLayerRow l))) =
      some pub.1.pkRoot := by
    rw [← hTop]
    simpa only [hSH, Nat.reducePow, Nat.pow_one, Nat.reduceAdd] using hUp
  have hCur0 : cur 0 = (stepRegsAt R 571).curRoot := by rw [hcur]
  rw [hCur0] at hL0
  rw [hMu] at hXof
  simpa only [stepCordSig,
    show corduroyPoseidon2Geom.profile = AggSigProfile.corduroyPoseidon2 by
      simp only [corduroyPoseidon2Geom.public_eqs],
    show List.range' 0 16 = 0 :: List.range' 1 15 from rfl, List.map_cons] using
    verifyAggNativeSig_stateless_intro corduroyPoseidon2Geom pub.1 msg (stepAuxLane R 1 0)
    _ (stepCordLayerSig R (stepCordLayerRow 0))
    ((List.range' 1 15).map (fun l => stepCordLayerSig R (stepCordLayerRow l)))
    leaf ((List.range' 0 32).map (stepForsIdx m)) (stepRegsAt R 571).curRoot (cur 1)
    (by simp only [corduroyPoseidon2Geom.public_eqs]; decide +kernel)
    (by simpa only [corduroyPoseidon2Geom.public_eqs] using hProf)
    (by simp only [List.length_cons, List.length_map, List.length_range', corduroyPoseidon2Geom.public_eqs])
    (by simp only [corduroyPoseidon2Geom.public_eqs]; decide +kernel) hXof hFors hL0 hUp'

/-- Executable decision and witness extraction for an active stateless slot. The success
    branch contains the native signature itself. -/
def extractCorduroySlotOrReject (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .corduroyPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    PSum { sig : AggNativeSignature //
        verifyAggNativeSig corduroyPoseidon2Geom pub.1 msg sig = true }
      (stepOp256TableOk .corduroyPoseidon2 slots rows = false) :=
  if h : stepOp256TableOk .corduroyPoseidon2 slots rows = true then
    .inl ⟨stepCordSig (stepOpSlotRow .corduroyPoseidon2 rows k),
      stepOp256TableOk_corduroy_extract slots rows k pub msg h hSlot hProf hMu⟩
  else .inr (Bool.eq_false_iff.mpr h)

/-- The rows of each hypertree layer inside a `CorduroyPoseidon2` signer block. -/
private theorem stepCordRun_layer {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    (hRun0 : StepRunAt pub R (signerProgramBody .corduroyPoseidon2) 0) :
    ∀ l < 16, StepRunAt pub R (stepCordLayerOps l (l + 1 == 16)) (571 + l * 465) := by
  have hRun : StepRunAt pub R
      ((((stepDeriveOps ++ [StepOp.forsRootsSpongeInit]) ++
          (List.range 16).flatMap stepForsPairOps) ++ [StepOp.forsRootsFinalSqueeze]) ++
        (List.range 16).flatMap (fun layer => stepCordLayerOps layer (layer + 1 == 16))) 0 := by
    simpa only [signerProgramBody.public_eqs, stepDeriveOps, stepForsPairOps_fun,
      stepCordLayerOps, List.append_assoc] using hRun0
  have hlenPre : ((stepDeriveOps ++ [StepOp.forsRootsSpongeInit]) ++
      (List.range 16).flatMap stepForsPairOps).length = 570 := by
    rw [List.length_append, flatMap_range_uniform_length _ 35 stepForsPairOps_length]
    rfl
  have hLayers : StepRunAt pub R
      ((List.range 16).flatMap (fun layer => stepCordLayerOps layer (layer + 1 == 16))) 571 := by
    have h := hRun.append_right
    rw [List.length_append, hlenPre] at h
    exact h
  exact StepRunAt.flatMap_range (L := 465) (fun l => stepCordLayerOps_length l _) 16 hLayers

/-- A stateless block whose last Merkle row does not hash to the public-key root is rejected:
    the extraction theorem's acceptance hypothesis is sensitive to the top-layer root. -/
theorem tooth_stepOp256_corduroy_wrong_top_root_rejected (slots : List StepOpSlot)
    (rows : List StepOpRow) (k : Nat) (pub : AggValidatorPk × Digest5)
    (hSlot : slots[k]? = some (some pub))
    (hWrong : (poseidon2Perm12 (stepOpSlotRow .corduroyPoseidon2 rows k 8010).stIn).b0 ≠
      pub.1.pkRoot) :
    stepOp256TableOk .corduroyPoseidon2 slots rows = false := by
  apply Bool.eq_false_iff.mpr
  intro hTable
  have hRun0 := stepOp256TableOk_slot_run .corduroyPoseidon2 slots rows k pub hTable hSlot
  have hTop : StepRowSem pub (stepOpSlotRow .corduroyPoseidon2 rows k)
      (.xmssMerkleBlockB true true) 8010 :=
    (stepCordRun_layer hRun0 15 (by decide)).get 464 _ (stepCordLayerOps_last 15 true)
  exact hWrong (stepSem_xmssMerkleBlockB_top hTop).2.2

#tooth_pair stepOp256TableOk_corduroy_extract vs tooth_stepOp256_corduroy_wrong_top_root_rejected

/-- Read every stateless signature from its accepted machine block in committee order. -/
def corduroyCommitteeSigs (stmt : AggArithPublicStmt) (rows : List StepOpRow) :
    List AggNativeSignature :=
  (List.range stmt.committeePks.length).map
    (fun k => stepCordSig (stepOpSlotRow .corduroyPoseidon2 rows k))

/-- Whole-committee soundness of the stateless machine extractor. -/
theorem corduroyCommitteeSigs_valid (stmt : AggArithPublicStmt) (rows : List StepOpRow)
    (hGeom : stmt.geom = corduroyPoseidon2Geom) (hWf : stmt.wellFormed = true)
    (hTable : stepOp256TableOk .corduroyPoseidon2 (xmssCommitteeSlots stmt) rows = true) :
    (corduroyCommitteeSigs stmt rows).length = stmt.committeePks.length ∧
    ∀ (k : Nat) (hkP : k < stmt.committeePks.length)
      (hkS : k < (corduroyCommitteeSigs stmt rows).length),
      verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg
        ((corduroyCommitteeSigs stmt rows)[k]'hkS) = true := by
  refine ⟨by simp [corduroyCommitteeSigs], ?_⟩
  intro k hkP hkS
  have hpks : stmt.committeePks.all (·.profile == stmt.geom.profile) = true :=
    (Bool.and_eq_true_iff.mp hWf).2
  have hp : (stmt.committeePks[k]'hkP).profile = .corduroyPoseidon2 := by
    have h := eq_of_beq (List.all_eq_true.mp hpks _ (List.getElem_mem hkP))
    simpa only [hGeom, corduroyPoseidon2Geom.public_eqs] using h
  have hs : (xmssCommitteeSlots stmt)[k]? =
      some (some (stmt.committeePks[k]'hkP, computeMessageMu (stmt.committeePks[k]'hkP) stmt.msg)) := by
    simp [xmssCommitteeSlots, List.getElem?_eq_getElem hkP]
  simpa [corduroyCommitteeSigs, hGeom] using
    stepOp256TableOk_corduroy_extract (xmssCommitteeSlots stmt) rows k
      (stmt.committeePks[k]'hkP, computeMessageMu (stmt.committeePks[k]'hkP) stmt.msg)
      stmt.msg hTable hs hp rfl

/-- Construct the serialized trace from the machine-extracted stateless signatures. -/
def corduroyMachineToExecutionTrace (stmt : AggArithPublicStmt) (rows : List StepOpRow) :
    AggExecutionTrace := buildHonestAggExecutionTrace stmt (corduroyCommitteeSigs stmt rows)

/-- **256-column to serialized-trace bridge, stateless profile.** An accepted 256-column table
    over the committee's active slots yields an accepted serialized execution trace. -/
theorem corduroyMachineToExecutionTrace_accepts (stmt : AggArithPublicStmt)
    (rows : List StepOpRow)
    (hGeom : stmt.geom = corduroyPoseidon2Geom) (hWf : stmt.wellFormed = true)
    (hTable : stepOp256TableOk .corduroyPoseidon2 (xmssCommitteeSlots stmt) rows = true) :
    traceSatisfiesAllConstraints stmt (corduroyMachineToExecutionTrace stmt rows) = true := by
  obtain ⟨hLen, hAll⟩ := corduroyCommitteeSigs_valid stmt rows hGeom hWf hTable
  exact buildHonestAggExecutionTrace_satisfies_constraints stmt _ hWf hLen hAll

end HemStepOp256Machine
end Qsag
end

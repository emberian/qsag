module
/-
# Register View of the 44 Carried Limbs and Per-Opcode Row Semantics

The register view `StepRegs` of the carried state limbs with the packed remaining-step
counters `StepRem`, the row-to-row register update of every scheduled opcode, and the
per-opcode row semantics `stepSem_*` derived from the guard and transition residuals of an
accepted row.
-/

public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.StepOp256SelectorEquiv

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

/-! ### §3.5. Register view of the 44 carried limbs and per-opcode row semantics -/

private theorem allZero_nil : allZeroGoldilocks [] = true := by rw [allZeroGoldilocks_eq]; rfl

private theorem allZero_cons (r : Goldilocks) (rs : List Goldilocks) :
    allZeroGoldilocks (r :: rs) = ((r == Goldilocks.zero) && allZeroGoldilocks rs) := by rw [allZeroGoldilocks_eq, allZeroGoldilocks_eq]; rfl

theorem allZero_getElem {l : List Goldilocks} (h : allZeroGoldilocks l = true)
    (k : Nat) (hk : k < l.length) : l[k] = Goldilocks.zero := by
  simp only [allZeroGoldilocks_eq] at h
  exact beq_iff_eq.mp (List.all_eq_true.mp h _ (List.getElem_mem hk))

theorem g_ofNat_self (a : Goldilocks) : Goldilocks.ofNat a.val = a :=
  Goldilocks.ext (Nat.mod_eq_of_lt a.isLt)

private theorem g_sub_zero (a : Goldilocks) : a -ₚ Goldilocks.zero = a :=
  LawfulCommRing.sub_zero a

/-- The six `ST_REM_PACK` limbs. -/
structure StepRem where
  r0 : Goldilocks
  r1 : Goldilocks
  r2 : Goldilocks
  r3 : Goldilocks
  r4 : Goldilocks
  r5 : Goldilocks

/-- Limb `i` of `ST_REM_PACK` (zero outside the block). -/
@[expose] def StepRem.get (m : StepRem) : Nat → Goldilocks
  | 0 => m.r0
  | 1 => m.r1
  | 2 => m.r2
  | 3 => m.r3
  | 4 => m.r4
  | 5 => m.r5
  | _ => Goldilocks.zero

/-- Overwrite limb `i` of `ST_REM_PACK`. -/
def StepRem.set (m : StepRem) (i : Nat) (v : Goldilocks) : StepRem :=
  match i with
  | 0 => { m with r0 := v }
  | 1 => { m with r1 := v }
  | 2 => { m with r2 := v }
  | 3 => { m with r3 := v }
  | 4 => { m with r4 := v }
  | 5 => { m with r5 := v }
  | _ => m
#export_eqns StepRem.set

theorem StepRem.get_set (m : StepRem) (i j : Nat) (v : Goldilocks) (hi : i < 6) :
    (m.set i v).get j = if j = i then v else m.get j := by
  rcases i with _ | _ | _ | _ | _ | _ | i
  all_goals first
    | omega
    | (rcases j with _ | _ | _ | _ | _ | _ | j <;> first | rfl | (simp [StepRem.get, StepRem.set]))

/-- The carried state `st[0..44]` grouped by the register blocks of `trace.rs`. -/
structure StepRegs where
  curRoot : Lane4
  kp      : Goldilocks
  treeLo  : Goldilocks
  treeHi  : Goldilocks
  rem     : StepRem
  main    : Poseidon2State12
  sub     : Poseidon2State12
  work    : Lane4
  cursor  : Goldilocks
  acc     : Goldilocks
  u2      : Goldilocks

/-- Register view of a limb assignment. -/
@[expose] def stepRegs (s : Nat → Goldilocks) : StepRegs :=
  { curRoot := ⟨s 0, s 1, s 2, s 3⟩
    kp := s 4
    treeLo := s 5
    treeHi := s 6
    rem := ⟨s 7, s 8, s 9, s 10, s 11, s 12⟩
    main := ⟨⟨s 13, s 14, s 15, s 16⟩, ⟨s 17, s 18, s 19, s 20⟩, ⟨s 21, s 22, s 23, s 24⟩⟩
    sub := ⟨⟨s 25, s 26, s 27, s 28⟩, ⟨s 29, s 30, s 31, s 32⟩, ⟨s 33, s 34, s 35, s 36⟩⟩
    work := ⟨s 37, s 38, s 39, s 40⟩
    cursor := s 41
    acc := s 42
    u2 := s 43 }

private theorem stepRegs_congr {s s' : Nat → Goldilocks} (h : ∀ j < 44, s j = s' j) :
    stepRegs s = stepRegs s' := by
  unfold stepRegs
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide), h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide), h 24 (by decide), h 25 (by decide), h 26 (by decide), h 27 (by decide), h 28 (by decide), h 29 (by decide), h 30 (by decide), h 31 (by decide), h 32 (by decide), h 33 (by decide), h 34 (by decide), h 35 (by decide), h 36 (by decide), h 37 (by decide), h 38 (by decide), h 39 (by decide), h 40 (by decide), h 41 (by decide), h 42 (by decide), h 43 (by decide)]

/-- Registers entering row `t`. -/
@[expose] def stepRegsAt (R : Nat → StepOpRow) (t : Nat) : StepRegs := stepRegs (stepPrev R t)

/-- `poseidon2Perm12` of the `COL_ST_IN` block of row `t`. -/
@[expose] def stepPermAt (R : Nat → StepOpRow) (t : Nat) : Poseidon2State12 := poseidon2Perm12 (R t).stIn

/-- Weighted Jive feed-forward of row `t` on the lane `v`:
    `perm.b0 + v + 2·st_in[4..8] + 4·st_in[8..12]`, the value every chain-step and FORS-leaf row
    constrains (`poseidon2_compress12_ff` once `v` is the first block of `COL_ST_IN`). -/
def stepFfAt (R : Nat → StepOpRow) (t : Nat) (v : Lane4) : Lane4 :=
  lane4Add (stepPermAt R t).b0 (poseidon2WeightedFeedForward ⟨v, (R t).stIn.b1, (R t).stIn.b2⟩)
#export_eqns stepFfAt

/-- Four consecutive auxiliary cells of row `t`. -/
@[expose] def stepAuxLane (R : Nat → StepOpRow) (t base : Nat) : Lane4 :=
  ⟨stepAux R t base, stepAux R t (base + 1), stepAux R t (base + 2), stepAux R t (base + 3)⟩

/-- Limbwise selection `u * a + (1 - u) * c`. -/
def lane4Mux (u : Goldilocks) (a c : Lane4) : Lane4 :=
  ⟨(u *ₚ a.x0) +ₚ ((Goldilocks.one -ₚ u) *ₚ c.x0),
   (u *ₚ a.x1) +ₚ ((Goldilocks.one -ₚ u) *ₚ c.x1),
   (u *ₚ a.x2) +ₚ ((Goldilocks.one -ₚ u) *ₚ c.x2),
   (u *ₚ a.x3) +ₚ ((Goldilocks.one -ₚ u) *ₚ c.x3)⟩
#export_eqns lane4Mux

theorem lane4Mux_one (a c : Lane4) : lane4Mux Goldilocks.one a c = a := by
  unfold lane4Mux
  simp only [g_sub_self, g_zero_mul, g_add_zero, g_one_mul]

theorem lane4Mux_zero (a c : Lane4) : lane4Mux Goldilocks.zero a c = c := by
  unfold lane4Mux
  simp only [g_sub_zero, g_zero_mul, g_zero_add, g_one_mul]

/-- Row inputs with the permutation output replaced by `poseidon2Perm12` of `COL_ST_IN`. -/
@[expose] def stepOpRowInputsPerm (pub : AggValidatorPk × Digest5) (row : StepOpRow) : StepOpRowInputs :=
  { stepOpRowInputs pub row with
    permOut := fun i => (poseidon2Perm12 row.stIn).toList.getD i Goldilocks.zero }

theorem StepRowSem.inputs {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {op : StepOp} {t : Nat} (h : StepRowSem pub R op t) :
    stepOpRowInputs pub (R t) = stepOpRowInputsPerm pub (R t) := by
  simp only [stepOpRowInputsPerm, stepOpRowInputs.public_eqs]
  rw [h.1]

theorem StepRowSem.guard {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {op : StepOp} {t : Nat} (h : StepRowSem pub R op t) :
    allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2) (stepOpRowInputsPerm pub (R t))) = true := by
  rw [← h.inputs]
  exact h.2.1

theorem StepRowSem.regs {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {op : StepOp} {t : Nat} (h : StepRowSem pub R op t) :
    stepRegsAt R (t + 1) =
      stepRegs (stepOpExpectedNext (stepOpKindAndC0 op).1
        (Goldilocks.ofNat (stepOpKindAndC0 op).2) (stepOpRowInputsPerm pub (R t))) := by
  rw [← h.inputs]
  exact stepRegs_congr h.2.2

theorem state12_ext12 {s : Poseidon2State12}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Goldilocks}
    (h0 : s.b0.x0 = a0) (h1 : s.b0.x1 = a1) (h2 : s.b0.x2 = a2) (h3 : s.b0.x3 = a3)
    (h4 : s.b1.x0 = a4) (h5 : s.b1.x1 = a5) (h6 : s.b1.x2 = a6) (h7 : s.b1.x3 = a7)
    (h8 : s.b2.x0 = a8) (h9 : s.b2.x1 = a9) (h10 : s.b2.x2 = a10) (h11 : s.b2.x3 = a11) :
    s = ⟨⟨a0, a1, a2, a3⟩, ⟨a4, a5, a6, a7⟩, ⟨a8, a9, a10, a11⟩⟩ :=
  Poseidon2State12.ext (Lane4.ext h0 h1 h2 h3) (Lane4.ext h4 h5 h6 h7) (Lane4.ext h8 h9 h10 h11)

/-- The all-zero `ST_REM_PACK` block. -/
@[expose] def stepRemZero : StepRem :=
  ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
    Goldilocks.zero⟩

/-- The FORS leaf index read from the four base-4 digits `aux[4..8]`. -/
@[expose] def stepForsIdxF (R : Nat → StepOpRow) (t : Nat) : Goldilocks :=
  stepWeightedSum (fun k => stepAux R t (4 + k)) (fun k => 4 ^ k) 4

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

/-- The tweak block `[domain, addr, tree_lo, tree_hi]` of a WOTS+C chain step. -/
def stepWotsTweak (r : StepRegs) (c0 : Nat) : Lane4 :=
  ⟨domainWotsStep, ‹c0› +ₚ (r.kp *ₚ ‹2 ^ 16›), r.treeLo, r.treeHi⟩
#export_eqns stepWotsTweak

theorem stepSem_wotsTellInit {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer t : Nat} (h : StepRowSem pub R (.wotsTellInit layer) t) :
    (R t).stIn =
      ⟨pub.1.pkSeed,
       ⟨‹layer * 2 ^ 32› +ₚ (stepRegsAt R t).kp, (stepRegsAt R t).treeLo,
        (stepRegsAt R t).treeHi, ‹128›⟩,
       ⟨domainWotsPk, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gzz% hG 9)
    (gzz% hG 10) (gz% hG 11), (regs% h)⟩

theorem stepSem_wotsChainStep1 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer chain t : Nat} (h : StepRowSem pub R (.wotsChainStep1 layer chain) t) :
    (R t).stIn =
      ⟨(stepRegsAt R t).work, pub.1.pkSeed,
       stepWotsTweak (stepRegsAt R t) (layer * 2 ^ 44 + chain * 2 ^ 4 + 1)⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        work := lane4Mux (stepRegsAt R t).acc (stepRegsAt R t).work
          (stepFfAt R t (stepRegsAt R t).work) } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 1) (gz% hG 3)
    (gz% hG 5) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), (regs% h)⟩


theorem allZero_take {l : List Goldilocks} (h : allZeroGoldilocks l = true) (n : Nat) :
    allZeroGoldilocks (l.take n) = true := by
  simp only [allZeroGoldilocks_eq] at h ⊢
  exact List.all_eq_true.mpr fun x hx => List.all_eq_true.mp h x (List.mem_of_mem_take hx)

/-- Limbwise selection `(1 - u) * a + u * c` (the left child of a Merkle node). -/
@[expose] def lane4MuxL (u : Goldilocks) (a c : Lane4) : Lane4 :=
  ⟨((Goldilocks.one -ₚ u) *ₚ a.x0) +ₚ (u *ₚ c.x0),
   ((Goldilocks.one -ₚ u) *ₚ a.x1) +ₚ (u *ₚ c.x1),
   ((Goldilocks.one -ₚ u) *ₚ a.x2) +ₚ (u *ₚ c.x2),
   ((Goldilocks.one -ₚ u) *ₚ a.x3) +ₚ (u *ₚ c.x3)⟩

theorem lane4MuxL_zero (a c : Lane4) : lane4MuxL Goldilocks.zero a c = a := by
  unfold lane4MuxL
  simp only [g_sub_zero, g_zero_mul, g_add_zero, g_one_mul]

theorem lane4MuxL_one (a c : Lane4) : lane4MuxL Goldilocks.one a c = c := by
  unfold lane4MuxL
  simp only [g_sub_self, g_zero_mul, g_zero_add, g_one_mul]

/-- `st_in` of a final sponge squeeze: `main_sponge + [1, 0, ..]`. -/
@[expose] def stepSqueezeIn (r : StepRegs) : Poseidon2State12 :=
  ⟨⟨r.main.b0.x0 +ₚ Goldilocks.one, r.main.b0.x1, r.main.b0.x2, r.main.b0.x3⟩,
   r.main.b1, r.main.b2⟩

/-- `st_in` of the second block of a 2-block Merkle node. -/
@[expose] def stepMerkleBIn (r : StepRegs) : Poseidon2State12 :=
  ⟨lane4Add r.sub.b0 r.work,
   ⟨r.sub.b1.x0 +ₚ Goldilocks.one, r.sub.b1.x1 +ₚ poseidon2IvTag, r.sub.b1.x2, r.sub.b1.x3⟩,
   r.sub.b2⟩

set_option maxHeartbeats 800000 in
theorem stepSem_wotsChainStep0 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer chain slot t : Nat} (hs : slot < 6)
    (h : StepRowSem pub R (.wotsChainStep0 layer chain slot) t) :
    (stepAux R t 4 = Goldilocks.zero ∨ stepAux R t 4 = Goldilocks.one) ∧
    (stepAux R t 5 = Goldilocks.zero ∨ stepAux R t 5 = Goldilocks.one) ∧
    (stepAux R t 6 = Goldilocks.zero ∨ stepAux R t 6 = Goldilocks.one) ∧
    stepAux R t 5 *ₚ (Goldilocks.one -ₚ stepAux R t 4) = Goldilocks.zero ∧
    stepAux R t 6 *ₚ (Goldilocks.one -ₚ stepAux R t 5) = Goldilocks.zero ∧
    (stepRegsAt R t).rem.get slot =
      (‹3› -ₚ ((stepAux R t 4 +ₚ stepAux R t 5) +ₚ stepAux R t 6)) +ₚ
        (stepAux R t 7 *ₚ ‹4›) ∧
    (R t).stIn =
      ⟨stepAuxLane R t 0, pub.1.pkSeed,
       stepWotsTweak (stepRegsAt R t) (layer * 2 ^ 44 + chain * 2 ^ 4)⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := (stepRegsAt R t).rem.set slot (stepAux R t 7)
        work := lane4Mux (stepAux R t 4) (stepAuxLane R t 0)
          (stepFfAt R t (stepAuxLane R t 0))
        acc := stepAux R t 5
        u2 := stepAux R t 6 } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  step_guard_nf hG
  rcases slot with _ | _ | _ | _ | _ | _ | slot
  all_goals first
    | exact ⟨(stepBoolCheck_eq_zero_iff _).mp (gzz% hG 0),
        (stepBoolCheck_eq_zero_iff _).mp (gzz% hG 1),
        (stepBoolCheck_eq_zero_iff _).mp (gzz% hG 2), gzz% hG 3, gzz% hG 4, gz% hG 5,
        state12_ext12 (gz% hG 6) (gz% hG 8) (gz% hG 10) (gz% hG 12) (gz% hG 7) (gz% hG 9)
          (gz% hG 11) (gz% hG 13) (gz% hG 14) (gz% hG 15) (gz% hG 16) (gz% hG 17), (regs% h)⟩
    | exact absurd hs (by omega)

theorem stepSem_wotsChainStep2_odd {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer chain t : Nat} (h : StepRowSem pub R (.wotsChainStep2 layer chain true) t) :
    (R t).stIn =
      ⟨(stepRegsAt R t).work, pub.1.pkSeed,
       stepWotsTweak (stepRegsAt R t) (layer * 2 ^ 44 + chain * 2 ^ 4 + 2)⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        work := lane4Mux (stepRegsAt R t).u2 (stepRegsAt R t).work
          (stepFfAt R t (stepRegsAt R t).work) } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 1) (gz% hG 3)
    (gz% hG 5) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), (regs% h)⟩

theorem stepSem_wotsChainStep2_even {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer chain t : Nat} (h : StepRowSem pub R (.wotsChainStep2 layer chain false) t) :
    (R t).stIn =
      ⟨(stepRegsAt R t).work, pub.1.pkSeed,
       stepWotsTweak (stepRegsAt R t) (layer * 2 ^ 44 + chain * 2 ^ 4 + 2)⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        sub := ⟨lane4Mux (stepRegsAt R t).u2 (stepRegsAt R t).work
            (stepFfAt R t (stepRegsAt R t).work),
          (stepRegsAt R t).sub.b1, (stepRegsAt R t).sub.b2⟩ } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 1) (gz% hG 3)
    (gz% hG 5) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), (regs% h)⟩

set_option maxHeartbeats 400000 in
theorem stepSem_wotsTellPairAbsorb {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {pair t : Nat} (h : StepRowSem pub R (.wotsTellPairAbsorb pair) t) :
    ((pair + 1 == 64) = true → ∀ s < 5, (stepRegsAt R t).rem.get s = Goldilocks.zero) ∧
    (R t).stIn =
      ⟨lane4Add (stepRegsAt R t).main.b0 (stepRegsAt R t).sub.b0,
       lane4Add (stepRegsAt R t).main.b1 (stepRegsAt R t).work, (stepRegsAt R t).main.b2⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG : allZeroGoldilocks (stepOpGuardResiduals (.wotsTellPairAbsorb (pair + 1 == 64))
      (Goldilocks.ofNat 0) (stepOpRowInputsPerm pub (R t))) = true := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  cases hp : (pair + 1 == 64)
  · rw [hp] at hG
    exact ⟨fun hc => absurd hc (by simp),
      state12_ext12 (gz% hG 0) (gz% hG 3) (gz% hG 6) (gz% hG 9) (gz% hG 1) (gz% hG 4)
        (gz% hG 7) (gz% hG 10) (gz% hG 2) (gz% hG 5) (gz% hG 8) (gz% hG 11), (regs% h)⟩
  · rw [hp] at hG
    refine ⟨fun _ s hs => ?_,
      state12_ext12 (gz% hG 5) (gz% hG 8) (gz% hG 11) (gz% hG 14) (gz% hG 6) (gz% hG 9)
        (gz% hG 12) (gz% hG 15) (gz% hG 7) (gz% hG 10) (gz% hG 13) (gz% hG 16), (regs% h)⟩
    rcases s with _ | _ | _ | _ | _ | s
    · exact gzz% hG 0
    · exact gzz% hG 1
    · exact gzz% hG 2
    · exact gzz% hG 3
    · exact gzz% hG 4
    · exact absurd hs (by omega)

theorem stepSem_wotsTellFinalSqueeze {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .wotsTellFinalSqueeze t) :
    (R t).stIn = stepSqueezeIn (stepRegsAt R t) ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with work := (stepPermAt R t).b0, cursor := (stepRegsAt R t).kp } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), (regs% h)⟩

theorem stepSem_xmssMerkleBlockA {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer lvl t : Nat} (h : StepRowSem pub R (.xmssMerkleBlockA layer lvl) t) :
    (stepAux R t 0 = Goldilocks.zero ∨ stepAux R t 0 = Goldilocks.one) ∧
    (stepRegsAt R t).cursor = (stepAux R t 0 +ₚ stepAux R t 1) +ₚ stepAux R t 1 ∧
    (R t).stIn =
      ⟨pub.1.pkSeed, lane4MuxL (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2),
       ⟨domainMerkleNode, ‹layer * 2 ^ 48 + (lvl + 1) * 2 ^ 32› +ₚ stepAux R t 1,
        (stepRegsAt R t).treeLo, (stepRegsAt R t).treeHi⟩⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        sub := stepPermAt R t
        work := lane4Mux (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2)
        cursor := stepAux R t 1 } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨(stepBoolCheck_eq_zero_iff _).mp (gzz% hG 0), gz% hG 1,
    state12_ext12 (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 8) (gz% hG 3) (gz% hG 5)
      (gz% hG 7) (gz% hG 9) (gz% hG 10) (gz% hG 11) (gz% hG 12) (gz% hG 13), (regs% h)⟩

theorem stepSem_xmssMerkleBlockB_inner {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {isTop : Bool} {t : Nat} (h : StepRowSem pub R (.xmssMerkleBlockB false isTop) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with work := (stepPermAt R t).b0 } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), (regs% h)⟩

theorem stepSem_xmssMerkleBlockB_top {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R (.xmssMerkleBlockB true true) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    (stepRegsAt R t).cursor = Goldilocks.zero ∧
    (stepPermAt R t).b0 = pub.1.pkRoot := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), gzz% hG 12,
    Lane4.ext (gz% hG 13) (gz% hG 14) (gz% hG 15) (gz% hG 16)⟩

theorem stepSem_statefulHmsgBlock0 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .statefulHmsgBlock0 t) :
    (∀ i < 6, stepAux R t i = Goldilocks.zero ∨ stepAux R t i = Goldilocks.one) ∧
    (∀ i < 32, stepAux R t (6 + i) = Goldilocks.zero ∨ stepAux R t (6 + i) = Goldilocks.one) ∧
    (R t).stIn =
      ⟨pub.1.pkSeed, pub.1.pkRoot,
       ⟨domainHMsgStateful,
        (stepWeightedSum (stepAux R t) (fun i => 2 ^ i) 6 *ₚ ‹2 ^ 32›) +ₚ
          stepWeightedSum (fun i => stepAux R t (6 + i)) (fun i => 2 ^ i) 32,
        pub.2.limb4, poseidon2IvTag⟩⟩ ∧
    stepRegsAt R (t + 1) =
      { curRoot := pub.1.pkRoot
        kp := stepWeightedSum (stepAux R t) (fun i => 2 ^ i) 6
        treeLo := Goldilocks.zero
        treeHi := Goldilocks.zero
        rem := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
          Goldilocks.zero, Goldilocks.zero⟩
        main := stepPermAt R t
        sub := state12Zero
        work := lane4Zero
        cursor := Goldilocks.zero
        acc := Goldilocks.zero
        u2 := Goldilocks.zero } := by
  have hG := h.guard
  simp only [stepOpKindAndC0.public_eqs, stepOpGuardResiduals, allZeroGoldilocks_append,
    Bool.and_eq_true] at hG
  obtain ⟨⟨⟨hA, hB⟩, hKeys⟩, hDomain⟩ := hG
  exact ⟨fun i hi => (stepBoolCheck_eq_zero_iff _).mp ((allZero_map_iff 6 _).mp hA i hi),
    fun i hi => (stepBoolCheck_eq_zero_iff _).mp ((allZero_map_iff 32 _).mp hB i hi),
    state12_ext12 (gz% hKeys 0) (gz% hKeys 2) (gz% hKeys 4) (gz% hKeys 6)
      (gz% hKeys 1) (gz% hKeys 3) (gz% hKeys 5) (gz% hKeys 7)
      (gz% hDomain 0) (gz% hDomain 1) (gz% hDomain 2) (gz% hDomain 3), (regs% h)⟩

theorem stepSem_statefulHmsgBlock1 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .statefulHmsgBlock1 t) :
    (R t).stIn =
      ⟨lane4Add (stepRegsAt R t).main.b0 (stepAuxLane R t 0),
       lane4Add (stepRegsAt R t).main.b1 ⟨pub.2.limb0, pub.2.limb1, pub.2.limb2, pub.2.limb3⟩,
       (stepRegsAt R t).main.b2⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 3) (gz% hG 6) (gz% hG 9) (gz% hG 1) (gz% hG 4)
    (gz% hG 7) (gz% hG 10) (gz% hG 2) (gz% hG 5) (gz% hG 8) (gz% hG 11), (regs% h)⟩

theorem stepSem_statefulHmsgSqueeze {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .statefulHmsgSqueeze t) :
    (R t).stIn = stepSqueezeIn (stepRegsAt R t) ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
          Goldilocks.zero, Goldilocks.zero⟩
        main := stepPermAt R t
        acc := Goldilocks.zero } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), (regs% h)⟩

/-- `HmsgDecompLimb l`: the limb decomposition gate holds, the target sum is checked on the
    last limb, and only `ST_REM_PACK` and the digit accumulator change. -/
theorem stepSem_hmsgDecompLimb {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {l t : Nat} (hl : l < 5) (h : StepRowSem pub R (.hmsgDecompLimb l) t) :
    allZeroGoldilocks (stepLimb63Decomp (stepOpRowInputsPerm pub (R t)) l) = true ∧
    (l = 4 → stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l stAccOrU1 = ‹192›) ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := ⟨stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 7,
          stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 8,
          stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 9,
          stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 10,
          stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 11,
          stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 12⟩
        acc := stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l stAccOrU1 } := by
  have hG := by simpa only [stepOpKindAndC0.public_eqs] using h.guard
  try simp only [stepOpKindAndC0.public_eqs] at hG
  have hD : allZeroGoldilocks (stepLimb63Decomp (stepOpRowInputsPerm pub (R t)) l) = true :=
    by
      have hParts := hG
      simp only [stepOpGuardResiduals, allZeroGoldilocks_append, Bool.and_eq_true] at hParts
      exact hParts.1
  rcases l with _ | _ | _ | _ | _ | l
  · exact ⟨hD, fun hc => absurd hc (by decide), (regs% h)⟩
  · exact ⟨hD, fun hc => absurd hc (by decide), (regs% h)⟩
  · exact ⟨hD, fun hc => absurd hc (by decide), (regs% h)⟩
  · exact ⟨hD, fun hc => absurd hc (by decide), (regs% h)⟩
  · exact ⟨hD, fun _ => gz% hG 33, (regs% h)⟩
  · exact absurd hl (by omega)

end HemStepOp256Machine
end Qsag
end

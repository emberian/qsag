module
/-
# Forward Direction: a Native `XmssPoseidon2` Signature Yields an Accepted Table

Every natively accepted `XmssPoseidon2` signature yields an accepted 256-column table
(`stepXmssRows_of_verify`), including committees with inactive slots
(`stepXmssSlotsRows_of_verify`).
-/

public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.StepOp256CorduroyExtraction

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
set_option autoImplicit false
set_option maxErrors 1000
set_option Elab.async false
set_option exponentiation.threshold 2048
attribute [local irreducible] poseidon2Perm12

/-! ## §4. Forward direction: a native `XmssPoseidon2` signature yields an accepted table -/

section StepOpForward

local infixl:65 " +ₚ " => Goldilocks.add
local infixl:70 " *ₚ " => Goldilocks.mul
local notation "‹" n "›" => Goldilocks.ofNat n

/-- An instruction's free cells. The interpreter supplies all other columns. -/
structure StepForwardCells where
  input : Poseidon2State12
  aux : Fin 38 → Goldilocks

/-- Execute one instruction with honest permutation columns. -/
def stepForwardRow (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells) : StepOpRow :=
  populateStepOpNext (stepOpKindAndC0 op).1 (Goldilocks.ofNat (stepOpKindAndC0 op).2) pub
    (stepOpHonestPermutationRow cells.input prev [] (List.ofFn cells.aux))

/-- Execute a list of instructions, passing the entire next state to the following row. -/
def stepForwardRun (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells) :
    List StepOp → List Goldilocks → List StepOpRow
  | [], _ => []
  | op :: ops, prev =>
    let row := stepForwardRow pub op prev (supply op prev)
    row :: stepForwardRun pub supply ops row.nextState

theorem stepForwardRun_length (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) :
    (stepForwardRun pub supply ops prev).length = ops.length := by
  induction ops generalizing prev with
  | nil => rfl
  | cons op ops ih => simp only [stepForwardRun, List.length_cons, ih]

theorem stepForwardRow_groupA (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells) :
    allZeroGoldilocks (stepOpPermTrace (stepForwardRow pub op prev cells)).2 = true :=
  stepOpHonestPermutationRow_groupA cells.input prev _ _

theorem stepForwardRow_perm (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells) :
    (stepOpPermTrace (stepForwardRow pub op prev cells)).1 = poseidon2Perm12 cells.input :=
  stepOp256_groupA_exact _ (stepForwardRow_groupA pub op prev cells)

theorem stepForwardRow_next_length (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells) :
    (stepForwardRow pub op prev cells).nextState.length = 44 := by
  simp only [stepForwardRow, populateStepOpNext, List.length_map, List.length_range]

theorem stepForwardRow_wellShaped (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells) (hp : prev.length = 44) :
    (stepForwardRow pub op prev cells).wellShaped = true :=
  stepOpHonestPermutationRow_wellShaped cells.input prev _ _ hp
    (stepForwardRow_next_length pub op prev cells) List.length_ofFn

/-- All opcode converses share this transition constructor; only the guards remain. -/
theorem stepForwardRow_constraints_iff (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells)
    (hv : (stepOpKindAndC0 op).1.validSlot = true) :
    allZeroGoldilocks (stepOpConstraints (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs pub (stepForwardRow pub op prev cells))) = true ↔
    allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs pub (stepOpHonestPermutationRow cells.input prev []
        (List.ofFn cells.aux)))) = true :=
  populateStepOpNext_constraints_iff _ _ _ _ hv

theorem stepForwardRun_wellShaped (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) (hp : prev.length = 44) :
    ∀ row ∈ stepForwardRun pub supply ops prev, row.wellShaped = true := by
  induction ops generalizing prev with
  | nil => simp [stepForwardRun]
  | cons op ops ih =>
    intro row hr
    simp only [stepForwardRun, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact stepForwardRow_wellShaped _ _ _ _ hp
    · exact ih _ (stepForwardRow_next_length ..) _ hr

theorem stepForwardRun_groupA (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) :
    ∀ row ∈ stepForwardRun pub supply ops prev,
      allZeroGoldilocks (stepOpPermTrace row).2 = true := by
  induction ops generalizing prev with
  | nil => simp [stepForwardRun]
  | cons op ops ih =>
    intro row hr
    simp only [stepForwardRun, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact stepForwardRow_groupA ..
    · exact ih _ _ hr

theorem stepForwardRun_first (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) (row : StepOpRow)
    (h : (stepForwardRun pub supply ops prev)[0]? = some row) :
    row.prevState = prev := by
  cases ops with
  | nil => simp [stepForwardRun] at h
  | cons op ops =>
    simp only [stepForwardRun, List.getElem?_cons_zero, Option.some.injEq] at h
    subst row
    rfl

theorem stepForwardRun_shift (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) :
    ∀ i r r', (stepForwardRun pub supply ops prev)[i]? = some r →
      (stepForwardRun pub supply ops prev)[i + 1]? = some r' →
      r.nextState = r'.prevState := by
  induction ops generalizing prev with
  | nil => simp [stepForwardRun]
  | cons op ops ih =>
    intro i r r' hr hr'
    cases i with
    | zero =>
      simp only [stepForwardRun, List.getElem?_cons_zero, Option.some.injEq] at hr
      subst r
      exact (stepForwardRun_first _ _ _ _ _ hr').symm
    | succ i =>
      simp only [stepForwardRun, List.getElem?_cons_succ] at hr hr'
      exact ih _ i r r' hr hr'

/-- Recover the exact instruction and incoming state used to build a row. -/
theorem stepForwardRun_at (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) :
    ∀ (i : Nat) row, (stepForwardRun pub supply ops prev)[i]? = some row →
      ∃ op state, ops[i]? = some op ∧
        row = stepForwardRow pub op state (supply op state) := by
  induction ops generalizing prev with
  | nil => simp [stepForwardRun]
  | cons op ops ih =>
    intro i row hr
    cases i with
    | zero =>
      simp only [stepForwardRun, List.getElem?_cons_zero, Option.some.injEq] at hr
      exact ⟨op, prev, rfl, hr.symm⟩
    | succ i =>
      simp only [stepForwardRun, List.getElem?_cons_succ] at hr
      exact ih _ i row hr


/-- Zero register file used at every signer boundary. -/
def stepForwardZero : List Goldilocks := List.replicate 44 Goldilocks.zero

/-- Execute the padded program of a signer. -/
def stepForwardBlock (profile : AggSigProfile) (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells) : List StepOpRow :=
  stepForwardRun pub supply (buildSignerProgram profile) stepForwardZero

theorem stepForwardBlock_length (profile : AggSigProfile) (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells) :
    (stepForwardBlock profile pub supply).length = stepOpRowsPerSigner profile := by
  rw [stepForwardBlock, stepForwardRun_length]
  cases profile
  · simpa only [stepOpRowsPerSigner.public_eqs] using buildSignerProgram_length.2.2.1
  · simpa only [stepOpRowsPerSigner.public_eqs] using buildSignerProgram_length.2.2.2

theorem stepForwardBlock_boundary (profile : AggSigProfile) (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells) (i : Nat) (row : StepOpRow)
    (hr : (stepForwardBlock profile pub supply)[i]? = some row) :
    allZeroGoldilocks (stepOpBoundaryResiduals (stepOpRowsPerSigner profile) i row) = true := by
  apply (stepOpBoundaryResiduals_iff _ _ _).mpr
  constructor
  · intro j _ hi
    subst i
    have hp := stepForwardRun_first pub supply (buildSignerProgram profile) stepForwardZero row hr
    rw [hp]
    exact getD_replicate_zero 44 j
  · intro j hj hi
    obtain ⟨op, state, hop, rfl⟩ := stepForwardRun_at pub supply
      (buildSignerProgram profile) stepForwardZero i row hr
    have hi' : i = stepOpRowsPerSigner profile - 1 := by omega
    have hop' : op = .idle := by
      have h := stepForwardProgram_last profile
      rw [← hi', List.getD_eq_getElem?_getD, hop] at h
      exact h
    subst op
    simp only [stepForwardRow, populateStepOpNext, stepOpKindAndC0.public_eqs]
    change ((List.range 44).map (fun _ => Goldilocks.zero)).getD j Goldilocks.zero = _
    simp [List.getD_eq_getElem?_getD, hj]

/-- The complete interpreter satisfies the table checker exactly when its guards hold.
    Shape, permutation witnesses, boundary resets, and shifts need no hypotheses. -/
theorem stepForwardBlock_table_iff (profile : AggSigProfile) (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells) :
    stepOp256TableOk profile [some pub] (stepForwardBlock profile pub supply) = true ↔
    ∀ i row, (stepForwardBlock profile pub supply)[i]? = some row →
      allZeroGoldilocks (stepOpGuardResiduals
        (stepOpKindAndC0 ((buildSignerProgram profile).getD i .idle)).1
        (Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD i .idle)).2)
        (stepOpRowInputs pub row)) = true := by
  rw [stepOp256TableOk_iff_rows]
  have hn := stepForwardBlock_length profile pub supply
  have index : ∀ i row, (stepForwardBlock profile pub supply)[i]? = some row →
      i / stepOpRowsPerSigner profile = 0 ∧ i % stepOpRowsPerSigner profile = i := by
    intro i row hr
    have hi := (List.getElem?_eq_some_iff.mp hr).1
    rw [hn] at hi
    exact ⟨Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi⟩
  constructor
  · intro h i row hr
    obtain ⟨hd, hm⟩ := index i row hr
    have hz := h.2.2.2.1 i row hr
    simp only [hd, hm, List.getD_cons_zero] at hz
    exact ((stepOp256RowResiduals_active_iff profile pub i row).mp hz).2.2.2.1
  · intro hg
    refine ⟨by simp, by simpa using hn,
      stepForwardRun_wellShaped pub supply _ _ (List.length_replicate ..), ?_, ?_⟩
    · intro i row hr
      obtain ⟨hd, hm⟩ := index i row hr
      simp only [hd, hm, List.getD_cons_zero]
      simp only [stepOp256RowResiduals.public_eqs]
      rw [allZeroGoldilocks_append, allZeroGoldilocks_append, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨stepForwardRun_groupA pub supply _ _ row (List.mem_of_getElem? hr),
        stepForwardBlock_boundary profile pub supply i row hr⟩, ?_⟩
      obtain ⟨op, state, hop, he⟩ := stepForwardRun_at pub supply
        (buildSignerProgram profile) stepForwardZero i row hr
      have hopD : (buildSignerProgram profile).getD i .idle = op := by
        rw [List.getD_eq_getElem?_getD, hop]; rfl
      have hv := (buildSignerProgram_kind_mem_and_valid profile i).2
      rw [hopD] at hv ⊢
      apply (stepOpConstraints_iff_guard_and_next _ _ _ hv).mpr
      refine ⟨by simpa only [hopD] using hg i row hr, ?_⟩
      subst row
      intro j hj
      rw [stepForwardRow, populateStepOpNext_inputs, stepOpExpectedNext_congr_next]
      simp [stepOpRowInputs.public_eqs, List.getD_eq_getElem?_getD, hj]
    · intro i r r' hr hr' j _
      rw [stepForwardRun_shift pub supply _ _ i r r' hr hr']

/-- Read a four-limb auxiliary block, using zero for absent signature elements. -/
def stepForwardLane (f : Nat → Goldilocks) (base : Nat) : Lane4 :=
  ⟨f base, f (base + 1), f (base + 2), f (base + 3)⟩

/-- Auxiliary cells for the XMSS program. Out-of-profile instructions receive zeros. -/
def stepXmssAux (sig : AggNativeSignature) (op : StepOp)
    (prev : List Goldilocks) (i : Nat) : Goldilocks :=
  let ls := sig.layers.getD 0 ⟨0, [], []⟩
  let s := fun j => prev.getD j Goldilocks.zero
  match op with
  | .statefulHmsgBlock0 =>
    if i < 6 then Goldilocks.ofNat (sig.statefulLeafIdx / 2 ^ i % 2)
    else if i < 38 then Goldilocks.ofNat (ls.tswCtr / 2 ^ (i - 6) % 2)
    else Goldilocks.zero
  | .statefulHmsgBlock1 => sig.rRand.toList.getD i Goldilocks.zero
  | .hmsgDecompLimb l =>
    if i < 31 then Goldilocks.ofNat ((s (stMainSponge + l)).val / 4 ^ i % 4)
    else if i = 31 then Goldilocks.ofNat ((s (stMainSponge + l)).val / 2 ^ 62 % 2)
    else Goldilocks.zero
  | .wotsChainStep0 _ chain slot =>
    let rem := (s (stRemPack + slot)).val
    let digit := 3 - rem % 4
    if i < 4 then (ls.wotsChains.getD chain lane4Zero).toList.getD i Goldilocks.zero
    else if i < 7 then Goldilocks.ofNat (if i - 4 < digit then 1 else 0)
    else if i = 7 then Goldilocks.ofNat (rem / 4)
    else Goldilocks.zero
  | .xmssMerkleBlockA _ lvl =>
    if i = 0 then Goldilocks.ofNat ((s stCursorIdx).val % 2)
    else if i = 1 then Goldilocks.ofNat ((s stCursorIdx).val / 2)
    else if i < 6 then
      (ls.merklePath.getD lvl lane4Zero).toList.getD (i - 2) Goldilocks.zero
    else Goldilocks.zero
  | _ => Goldilocks.zero

/-- Permutation inputs for the XMSS program, expressed using the actual incoming registers. -/
def stepXmssInput (pk : AggValidatorPk) (mu : Digest5) (op : StepOp)
    (prev : List Goldilocks) (aux : Nat → Goldilocks) : Poseidon2State12 :=
  let r := stepRegs (fun j => prev.getD j Goldilocks.zero)
  let c0 := Goldilocks.ofNat (stepOpKindAndC0 op).2
  match op with
  | .statefulHmsgBlock0 =>
    ⟨pk.pkSeed, pk.pkRoot, ⟨domainHMsgStateful,
      stepWeightedSum aux (fun i => 2 ^ i) 6 *ₚ Goldilocks.ofNat (2 ^ 32) +ₚ
        stepWeightedSum (fun i => aux (6 + i)) (fun i => 2 ^ i) 32,
      mu.limb4, poseidon2IvTag⟩⟩
  | .statefulHmsgBlock1 =>
    ⟨lane4Add r.main.b0 (stepForwardLane aux 0),
      lane4Add r.main.b1 ⟨mu.limb0, mu.limb1, mu.limb2, mu.limb3⟩, r.main.b2⟩
  | .statefulHmsgSqueeze | .wotsTellFinalSqueeze => stepSqueezeIn r
  | .wotsTellInit _ =>
    ⟨pk.pkSeed, ⟨c0 +ₚ r.kp, r.treeLo, r.treeHi, Goldilocks.ofNat 128⟩,
      ⟨domainWotsPk, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩
  | .wotsChainStep0 _ _ _ =>
    ⟨stepForwardLane aux 0, pk.pkSeed,
      ⟨domainWotsStep, c0 +ₚ r.kp *ₚ Goldilocks.ofNat (2 ^ 16), r.treeLo, r.treeHi⟩⟩
  | .wotsChainStep1 _ _ | .wotsChainStep2 _ _ _ =>
    ⟨r.work, pk.pkSeed,
      ⟨domainWotsStep, c0 +ₚ r.kp *ₚ Goldilocks.ofNat (2 ^ 16), r.treeLo, r.treeHi⟩⟩
  | .wotsTellPairAbsorb _ =>
    ⟨lane4Add r.main.b0 r.sub.b0, lane4Add r.main.b1 r.work, r.main.b2⟩
  | .xmssMerkleBlockA _ _ =>
    ⟨pk.pkSeed, lane4MuxL (aux 0) r.work (stepForwardLane aux 2),
      ⟨domainMerkleNode, c0 +ₚ aux 1, r.treeLo, r.treeHi⟩⟩
  | .xmssMerkleBlockB _ _ => stepMerkleBIn r
  | _ => state12Zero

/-- Signature-driven free columns for a single XMSS instruction. -/
def stepXmssCells (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (op : StepOp) (prev : List Goldilocks) : StepForwardCells :=
  ⟨stepXmssInput pk mu op prev (stepXmssAux sig op prev),
    fun i => stepXmssAux sig op prev i.val⟩

/-- The explicit 512-row XMSS signer block, including honest padding permutations. -/
def stepXmssRows (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) : List StepOpRow :=
  stepForwardBlock .xmssPoseidon2 (pk, mu) (stepXmssCells pk mu sig)

theorem stepXmssRows_length (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    (stepXmssRows pk mu sig).length = 512 := by
  simpa only [stepXmssRows, stepOpRowsPerSigner.public_eqs] using
    stepForwardBlock_length .xmssPoseidon2 (pk, mu) (stepXmssCells pk mu sig)

theorem stepXmssRows_wellShaped (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    ∀ row ∈ stepXmssRows pk mu sig, row.wellShaped = true :=
  stepForwardRun_wellShaped _ _ _ _ (List.length_replicate ..)

theorem stepXmssRows_groupA (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    ∀ row ∈ stepXmssRows pk mu sig, allZeroGoldilocks (stepOpPermTrace row).2 = true :=
  stepForwardRun_groupA _ _ _ _

theorem stepXmssRows_shift (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    allZeroGoldilocks (stepOp256ShiftResiduals (stepXmssRows pk mu sig)) = true := by
  apply (stepOp256ShiftResiduals_iff _).mpr
  intro i r r' hr hr' j _
  rw [stepForwardRun_shift (pk, mu) (stepXmssCells pk mu sig) _ _ i r r' hr hr']

/-- The exact remaining obligation for native-to-machine completeness. -/
def StepXmssGuards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) : Prop :=
  ∀ (i : Nat) row, (stepXmssRows pk mu sig)[i]? = some row →
    allZeroGoldilocks (stepOpGuardResiduals
      (stepOpKindAndC0 ((buildSignerProgram .xmssPoseidon2).getD i .idle)).1
      (Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram .xmssPoseidon2).getD i .idle)).2)
      (stepOpRowInputs (pk, mu) row)) = true

theorem stepXmssRows_table_iff (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    stepOp256TableOk .xmssPoseidon2 [some (pk, mu)] (stepXmssRows pk mu sig) = true ↔
      StepXmssGuards pk mu sig :=
  stepForwardBlock_table_iff ..

/-- Directly supplied cells of an XMSS instruction, before filling the next state. -/
def stepXmssSeedRow (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (op : StepOp) (prev : List Goldilocks) : StepOpRow :=
  stepOpHonestPermutationRow (stepXmssCells pk mu sig op prev).input prev []
    (List.ofFn (stepXmssCells pk mu sig op prev).aux)

/-- Opcodes whose guards impose no additional arithmetic or terminal checks. -/
def StepXmssPlainOp : StepOp → Prop
  | .idle | .statefulHmsgBlock1 | .statefulHmsgSqueeze | .wotsTellInit _
  | .wotsChainStep1 _ _ | .wotsChainStep2 _ _ _ | .wotsTellFinalSqueeze
  | .xmssMerkleBlockB false _ => True
  | _ => False

macro "step_forward_reduce" : tactic => `(tactic|
  simp only [stepOpKindAndC0.public_eqs, stepOpGuardResiduals,
    stepSpongeAbsorbInput.public_eqs, stepSqueezeInput.public_eqs, stepWotsStepInput.public_eqs, stepMerkleBlockBInput.public_eqs,
    stepOpRowInputs.public_eqs, stepXmssSeedRow, stepOpHonestPermutationRow, stepXmssCells,
    stepXmssInput, stepXmssAux, stepRegs, stepForwardLane, stepSqueezeIn, stepMerkleBIn,
    stMainSponge.public_eqs, stWork.public_eqs, stSubSponge.public_eqs, stTreeLo.public_eqs, stTreeHi.public_eqs, stKpIdx.public_eqs,
    List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.nil_append,
    List.append_nil, List.cons_append, List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    List.getElem?_ofFn, Option.getD_some, Option.getD_none,
    Poseidon2State12.toList_eq, Lane4.toList_eq, lane4Add_eq, lane4MuxL,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceBEq, Nat.reduceEqDiff,
    ↓reduceIte, Bool.false_eq_true, Bool.not_false, Bool.true_eq,
    g_sub_self, allZeroGoldilocks_eq, List.all_cons, List.all_nil,
    beq_self_eq_true, Bool.and_true, Bool.true_and, dite_true] )

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_plain_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (op : StepOp) (prev : List Goldilocks) (hop : StepXmssPlainOp op) :
    allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig op prev))) = true := by
  cases op <;> simp only [StepXmssPlainOp] at hop
  all_goals first | contradiction | skip
  case' xmssMerkleBlockB a b => cases a <;> simp only [StepXmssPlainOp] at hop
  all_goals first | contradiction | skip
  all_goals step_forward_reduce

/-- An inactive row still has honest Group A columns and zero boundary registers. -/
def stepInactiveRow : StepOpRow :=
  stepOpHonestPermutationRow state12Zero stepForwardZero stepForwardZero
    (List.replicate 38 Goldilocks.zero)

/-- Inactive signer blocks contain real permutation witnesses, not all-zero rows. -/
def stepInactiveRows (profile : AggSigProfile) : List StepOpRow :=
  List.replicate (stepOpRowsPerSigner profile) stepInactiveRow

theorem stepInactiveRow_residuals (profile : AggSigProfile) (t : Nat) :
    allZeroGoldilocks (stepOp256RowResiduals profile none t stepInactiveRow) = true := by
  simp only [stepOp256RowResiduals.public_eqs]
  rw [List.append_nil, allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨stepOpHonestPermutationRow_groupA .., ?_⟩
  apply (stepOpBoundaryResiduals_iff _ _ _).mpr
  exact ⟨fun j _ _ => getD_replicate_zero 44 j, fun j _ _ => getD_replicate_zero 44 j⟩

/-- A nonempty committee consisting entirely of inactive slots is accepted. -/
theorem stepInactiveCommittee_table (profile : AggSigProfile) (n : Nat) (hn : 0 < n) :
    stepOp256TableOk profile (List.replicate n none)
      (List.replicate (n * stepOpRowsPerSigner profile) stepInactiveRow) = true := by
  apply (stepOp256TableOk_iff_rows _ _ _).mpr
  refine ⟨by simpa using hn, by simp, ?_, ?_, ?_⟩
  · intro row hr
    have he := (List.mem_replicate.mp hr).2
    subst row
    exact stepOpHonestPermutationRow_wellShaped _ _ _ _
      (List.length_replicate ..) (List.length_replicate ..) (List.length_replicate ..)
  · intro i row hr
    have he := (List.mem_replicate.mp (List.mem_of_getElem? hr)).2
    subst row
    have hs : (List.replicate n (none : StepOpSlot)).getD
        (i / stepOpRowsPerSigner profile) none = none := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    rw [hs]
    exact stepInactiveRow_residuals _ _
  · intro i r r' hr hr' j _
    have he := (List.mem_replicate.mp (List.mem_of_getElem? hr)).2
    have he' := (List.mem_replicate.mp (List.mem_of_getElem? hr')).2
    subst r
    subst r'
    rfl

/-- Conditional round trip through the existing native extractor. -/
theorem stepXmssRows_extract (pk : AggValidatorPk) (msg : List UInt8)
    (sig : AggNativeSignature) (hp : pk.profile = .xmssPoseidon2)
    (hg : StepXmssGuards pk (computeMessageMu pk msg) sig) :
    verifyAggNativeSig xmssPoseidon2Geom pk msg
      (stepXmssSig (stepOpSlotRow .xmssPoseidon2
        (stepXmssRows pk (computeMessageMu pk msg) sig) 0)) = true :=
  stepOp256TableOk_xmss_extract _ _ 0 (pk, computeMessageMu pk msg) msg
    ((stepXmssRows_table_iff ..).mpr hg) rfl hp rfl

theorem stepXmssSeedRow_aux (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (op : StepOp) (prev : List Goldilocks) (i : Nat) (hi : i < 38) :
    (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig op prev)).aux i =
      stepXmssAux sig op prev i := by
  change (List.ofFn (fun j : Fin 38 => stepXmssAux sig op prev j.val)).getD i Goldilocks.zero = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]

/-- The decomposition cells satisfy the full limb gate whenever the native range check holds. -/
theorem stepXmss_limb63 (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (l : Nat)
    (h : (prev.getD (stMainSponge + l) Goldilocks.zero).val < 2 ^ 63) :
    allZeroGoldilocks (stepLimb63Decomp
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.hmsgDecompLimb l) prev)) l) = true := by
  apply (stepLimb63Decomp_allZero_iff _ _).mpr
  refine ⟨h, ?_, ?_⟩
  · intro i hi
    rw [stepXmssSeedRow_aux _ _ _ _ _ _ (by omega)]
    simp only [stepXmssAux, hi, ↓reduceIte]
    rfl
  · rw [stepXmssSeedRow_aux _ _ _ _ _ _ (by decide)]
    change Goldilocks.ofNat ((prev.getD (stMainSponge + l) Goldilocks.zero).val / 2 ^ 62 % 2) =
      Goldilocks.ofNat ((prev.getD (stMainSponge + l) Goldilocks.zero).val / 4 ^ 31)
    have he : (4 : Nat) ^ 31 = 2 ^ 62 := by decide +kernel
    rw [he, Nat.mod_eq_of_lt (by omega)]

/-- Hmsg decomposition has only the range and final digit-sum obligations. -/
theorem stepXmss_decomp_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (l : Nat)
    (h : (prev.getD (stMainSponge + l) Goldilocks.zero).val < 2 ^ 63)
    (hs : l = 4 → stepHmsgDecompExpected
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.hmsgDecompLimb l) prev))
        l stAccOrU1 = Goldilocks.ofNat 192) :
    allZeroGoldilocks (stepOpGuardResiduals (.hmsgDecompLimb l) (Goldilocks.ofNat 0)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.hmsgDecompLimb l) prev))) = true := by
  unfold stepOpGuardResiduals
  rw [allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨stepXmss_limb63 pk mu sig prev l h, ?_⟩
  by_cases hl : l = 4
  · simp only [ite_eq_left hl, hs hl, allZeroGoldilocks_eq, List.all_cons, List.all_nil,
      g_sub_self, beq_self_eq_true, Bool.and_self]
  · simp [hl, allZeroGoldilocks_eq]

/-- Canonical quotient and remainder also reconstruct the original field element. -/
theorem stepForward_div_mod (v : Goldilocks) (base : Nat) :
    v = Goldilocks.ofNat (v.val % base) +ₚ
      (Goldilocks.ofNat (v.val / base) *ₚ Goldilocks.ofNat base) := by
  rw [← g_ofNat_mul, ← g_ofNat_add]
  apply Goldilocks.ext
  rw [Goldilocks.ofNat_val, Nat.mul_comm (v.val / base), Nat.mod_add_div,
    Nat.mod_eq_of_lt v.isLt]

/-- Three monotone skip bits encode the digit complementary to the remaining count. -/
theorem stepForward_wots_flags (v : Goldilocks) :
    let b := fun k => Goldilocks.ofNat (if k < 3 - v.val % 4 then 1 else 0)
    allZeroGoldilocks [stepBoolCheck (b 0), stepBoolCheck (b 1), stepBoolCheck (b 2),
      b 1 *ₚ Goldilocks.sub Goldilocks.one (b 0),
      b 2 *ₚ Goldilocks.sub Goldilocks.one (b 1),
      Goldilocks.sub v (Goldilocks.sub (Goldilocks.ofNat 3) ((b 0 +ₚ b 1) +ₚ b 2) +ₚ
        (Goldilocks.ofNat (v.val / 4) *ₚ Goldilocks.ofNat 4))] = true := by
  dsimp only
  have hr := stepForward_div_mod v 4
  have hm : v.val % 4 = 0 ∨ v.val % 4 = 1 ∨ v.val % 4 = 2 ∨ v.val % 4 = 3 := by omega
  rcases hm with hm | hm | hm | hm
  all_goals rw [hm] at hr ⊢
  all_goals simp only [stepBoolCheck_eq]
  all_goals change allZeroGoldilocks [Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
    Goldilocks.zero, Goldilocks.zero, Goldilocks.sub v _] = true
  all_goals simp only [allZeroGoldilocks_eq, List.all_cons, List.all_nil,
    beq_self_eq_true, Bool.true_and, Bool.and_true, beq_iff_eq]
  all_goals exact g_sub_eq_zero_iff.mpr hr

/-- Cursor halving supplies both the direction bit and the parent index. -/
theorem stepForward_merkle_cursor (v : Goldilocks) :
    stepBoolCheck (Goldilocks.ofNat (v.val % 2)) = Goldilocks.zero ∧
    v = (Goldilocks.ofNat (v.val % 2) +ₚ Goldilocks.ofNat (v.val / 2)) +ₚ
      Goldilocks.ofNat (v.val / 2) := by
  constructor
  · have hm : v.val % 2 = 0 ∨ v.val % 2 = 1 := by omega
    rcases hm with hm | hm <;> rw [hm]
    · exact (stepBoolCheck_eq_zero_iff _).mpr (Or.inl rfl)
    · exact (stepBoolCheck_eq_zero_iff _).mpr (Or.inr rfl)
  · have hr := stepForward_div_mod v 2
    rw [← g_ofNat_add, ← g_ofNat_add]
    rw [← g_ofNat_mul, ← g_ofNat_add] at hr
    rw [show v.val % 2 + v.val / 2 + v.val / 2 = v.val % 2 + v.val / 2 * 2 by omega]
    exact hr

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_chain0_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (layer chain slot : Nat) :
    allZeroGoldilocks (stepOpGuardResiduals (.wotsChainStep0 slot)
      (Goldilocks.ofNat (layer * 2 ^ 44 + chain * 2 ^ 4))
      (stepOpRowInputs (pk, mu)
        (stepXmssSeedRow pk mu sig (.wotsChainStep0 layer chain slot) prev))) = true := by
  simp only [stepOpGuardResiduals, allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact stepForward_wots_flags (prev.getD (stRemPack + slot) Goldilocks.zero)
  all_goals step_forward_reduce

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_merkleA_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (layer lvl : Nat) :
    allZeroGoldilocks (stepOpGuardResiduals .xmssMerkleBlockA
      (Goldilocks.ofNat (layer * 2 ^ 48 + (lvl + 1) * 2 ^ 32))
      (stepOpRowInputs (pk, mu)
        (stepXmssSeedRow pk mu sig (.xmssMerkleBlockA layer lvl) prev))) = true := by
  simp only [stepOpGuardResiduals, stepMerkleBlockAGuards,
    allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h := stepForward_merkle_cursor (prev.getD stCursorIdx Goldilocks.zero)
    change allZeroGoldilocks [stepBoolCheck (Goldilocks.ofNat (_ % 2)),
      Goldilocks.sub (prev.getD stCursorIdx Goldilocks.zero)
        ((Goldilocks.ofNat (_ % 2) +ₚ Goldilocks.ofNat (_ / 2)) +ₚ Goldilocks.ofNat (_ / 2))] = true
    rw [h.1, ← h.2, g_sub_self]
    simp only [allZeroGoldilocks_eq, List.all_cons, List.all_nil, beq_self_eq_true, Bool.and_self]
  all_goals step_forward_reduce

theorem stepForward_bit (n : Nat) :
    stepBoolCheck (Goldilocks.ofNat (n % 2)) = Goldilocks.zero := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> rw [h]
  · exact (stepBoolCheck_eq_zero_iff _).mpr (Or.inl rfl)
  · exact (stepBoolCheck_eq_zero_iff _).mpr (Or.inr rfl)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_hmsg0_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) :
    allZeroGoldilocks (stepOpGuardResiduals .statefulHmsgBlock0 (Goldilocks.ofNat 0)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig .statefulHmsgBlock0 prev))) = true := by
  have hAux : (stepOpRowInputs (pk, mu)
      (stepXmssSeedRow pk mu sig .statefulHmsgBlock0 prev)).aux =
      stepXmssAux sig .statefulHmsgBlock0 prev := by
    funext i
    by_cases hi : i < 38
    · exact stepXmssSeedRow_aux _ _ _ _ _ _ hi
    · have h6 : ¬i < 6 := by omega
      change (List.ofFn (fun j : Fin 38 => stepXmssAux sig .statefulHmsgBlock0 prev j.val)).getD i _ = _
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, h6, stepXmssAux,
        ↓reduceDIte, ↓reduceIte, Option.getD_none]
  simp only [stepOpGuardResiduals, hAux, allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply (allZero_map_iff _ _).mpr
    intro i hi
    simp only [stepXmssAux, hi, ↓reduceIte, stepForward_bit]
  · apply (allZero_map_iff _ _).mpr
    intro i hi
    have hlo : ¬6 + i < 6 := by omega
    have hhi : 6 + i < 38 := by omega
    simp only [stepXmssAux, hlo, hhi, ↓reduceIte, stepForward_bit]
  · step_forward_reduce
  · step_forward_reduce

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_pair_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (pair : Nat)
    (h : pair + 1 = 64 → ∀ j < 5, prev.getD (stRemPack + j) Goldilocks.zero = Goldilocks.zero) :
    allZeroGoldilocks (stepOpGuardResiduals (.wotsTellPairAbsorb (pair + 1 == 64))
      (Goldilocks.ofNat 0)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.wotsTellPairAbsorb pair) prev))) = true := by
  simp only [stepOpGuardResiduals, allZeroGoldilocks_append, Bool.and_eq_true]
  constructor
  · by_cases hp : pair + 1 = 64
    · simp only [hp, beq_self_eq_true, ↓reduceIte]
      apply (allZero_map_iff _ _).mpr
      exact h hp
    · have hb : (pair + 1 == 64) = false := by exact beq_eq_false_iff_ne.mpr hp
      rw [hb]
      simp only [Bool.false_eq_true, ↓reduceIte, allZeroGoldilocks_eq, List.all_nil]
  · step_forward_reduce

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_merkleTop_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks)
    (hc : prev.getD stCursorIdx Goldilocks.zero = Goldilocks.zero)
    (hr : ∀ i < 4,
      (poseidon2Perm12 (stepXmssInput pk mu (.xmssMerkleBlockB true true) prev
        (stepXmssAux sig (.xmssMerkleBlockB true true) prev))).toList.getD i Goldilocks.zero =
        pk.pkRoot.toList.getD i Goldilocks.zero) :
    allZeroGoldilocks (stepOpGuardResiduals (.xmssMerkleBlockB true true) (Goldilocks.ofNat 0)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.xmssMerkleBlockB true true) prev))) = true := by
  simp only [stepOpGuardResiduals, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_⟩
  · step_forward_reduce
  · change allZeroGoldilocks [prev.getD stCursorIdx Goldilocks.zero] = true
    rw [hc]
    simp only [allZeroGoldilocks_eq, List.all_cons, List.all_nil, beq_self_eq_true, Bool.and_self]
  · apply (allZero_map_iff _ _).mpr
    intro i hi
    apply g_sub_eq_zero_iff.mpr
    have hp := stepOp256_groupA_exact
      (stepXmssSeedRow pk mu sig (.xmssMerkleBlockB true true) prev)
      (stepOpHonestPermutationRow_groupA ..)
    change (stepOpPermTrace _).1.toList.getD i Goldilocks.zero = _
    rw [hp]
    exact hr i hi




/-- Arithmetic and terminal checks left after supplying the honest local cells. -/
def StepXmssChecks (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (op : StepOp) (prev : List Goldilocks) : Prop :=
  match op with
  | .hmsgDecompLimb l =>
    (prev.getD (stMainSponge + l) Goldilocks.zero).val < 2 ^ 63 ∧
    (l = 4 → stepHmsgDecompExpected
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig op prev)) l stAccOrU1 =
        Goldilocks.ofNat 192)
  | .wotsTellPairAbsorb pair =>
    pair + 1 = 64 → ∀ j < 5, prev.getD (stRemPack + j) Goldilocks.zero = Goldilocks.zero
  | .xmssMerkleBlockB true true =>
    prev.getD stCursorIdx Goldilocks.zero = Goldilocks.zero ∧
    ∀ i < 4, (poseidon2Perm12 (stepXmssInput pk mu op prev (stepXmssAux sig op prev))).toList.getD
      i Goldilocks.zero = pk.pkRoot.toList.getD i Goldilocks.zero
  | _ => True

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_seed_guards_of_checks (pk : AggValidatorPk) (mu : Digest5)
    (sig : AggNativeSignature) (op : StepOp) (prev : List Goldilocks)
    (hs : stepXmssSupported op = true) (hc : StepXmssChecks pk mu sig op prev) :
    allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig op prev))) = true := by
  cases op <;> try simp only [stepXmssSupported.public_eqs] at hs
  all_goals try contradiction
  case idle => exact stepXmss_plain_guards pk mu sig .idle prev True.intro
  case statefulHmsgBlock0 => simpa only [stepOpKindAndC0.public_eqs] using stepXmss_hmsg0_guards pk mu sig prev
  case statefulHmsgBlock1 => exact stepXmss_plain_guards pk mu sig .statefulHmsgBlock1 prev True.intro
  case statefulHmsgSqueeze => exact stepXmss_plain_guards pk mu sig .statefulHmsgSqueeze prev True.intro
  case hmsgDecompLimb l => simpa only [stepOpKindAndC0.public_eqs] using stepXmss_decomp_guards pk mu sig prev l hc.1 hc.2
  case wotsTellInit l => exact stepXmss_plain_guards pk mu sig (.wotsTellInit l) prev True.intro
  case wotsChainStep0 l c slot => simpa only [stepOpKindAndC0.public_eqs] using stepXmss_chain0_guards pk mu sig prev l c slot
  case wotsChainStep1 l c => exact stepXmss_plain_guards pk mu sig (.wotsChainStep1 l c) prev True.intro
  case wotsChainStep2 l c odd => exact stepXmss_plain_guards pk mu sig (.wotsChainStep2 l c odd) prev True.intro
  case wotsTellPairAbsorb pair => simpa only [stepOpKindAndC0.public_eqs] using stepXmss_pair_guards pk mu sig prev pair hc
  case wotsTellFinalSqueeze => exact stepXmss_plain_guards pk mu sig .wotsTellFinalSqueeze prev True.intro
  case xmssMerkleBlockA l lvl => simpa only [stepOpKindAndC0.public_eqs] using stepXmss_merkleA_guards pk mu sig prev l lvl
  case xmssMerkleBlockB a b =>
    cases a with
    | false => exact stepXmss_plain_guards pk mu sig (.xmssMerkleBlockB false b) prev True.intro
    | true =>
      cases b with
      | false => simp only [stepXmssSupported.public_eqs, Bool.false_eq_true] at hs
      | true => simpa only [stepOpKindAndC0.public_eqs] using
        stepXmss_merkleTop_guards pk mu sig prev hc.1 hc.2


/-- A full active table follows from the remaining execution-wide checks.
    This statement uses the original checker, not a replacement acceptance predicate. -/
theorem stepXmssRows_table_of_checks (pk : AggValidatorPk) (mu : Digest5)
    (sig : AggNativeSignature)
    (hc : ∀ (i : Nat) row, (stepXmssRows pk mu sig)[i]? = some row →
      StepXmssChecks pk mu sig ((buildSignerProgram .xmssPoseidon2).getD i .idle) row.prevState) :
    stepOp256TableOk .xmssPoseidon2 [some (pk, mu)] (stepXmssRows pk mu sig) = true := by
  apply (stepXmssRows_table_iff pk mu sig).mpr
  intro i row hr
  obtain ⟨op, state, hop, he⟩ := stepForwardRun_at (pk, mu) (stepXmssCells pk mu sig)
    (buildSignerProgram .xmssPoseidon2) stepForwardZero i row hr
  have hs := List.all_eq_true.mp stepXmssProgram_supported op (List.mem_of_getElem? hop)
  have hopD : (buildSignerProgram .xmssPoseidon2).getD i .idle = op := by
    rw [List.getD_eq_getElem?_getD, hop]; rfl
  have hchecks := hc i row hr
  rw [hopD, he] at hchecks
  have hg := stepXmss_seed_guards_of_checks pk mu sig op state hs hchecks
  rw [hopD, he]
  change allZeroGoldilocks (stepOpGuardResiduals _ _
    (stepOpRowInputs (pk, mu) (populateStepOpNext _ _ _ (stepXmssSeedRow pk mu sig op state)))) = true
  rw [populateStepOpNext_inputs, stepOpGuardResiduals_congr_next]
  exact hg

/-- The constructed XMSS trace, indexed within its signer block. -/
def stepXmssR (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) : Nat → StepOpRow :=
  stepOpSlotRow .xmssPoseidon2 (stepXmssRows pk mu sig) 0

theorem stepXmssR_at (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (t : Nat) (ht : t < 512) :
    (stepXmssRows pk mu sig)[t]? = some (stepXmssR pk mu sig t) := by
  have hlt : t < (stepXmssRows pk mu sig).length := by rw [stepXmssRows_length]; exact ht
  simp only [stepXmssR, stepOpSlotRow.public_eqs, Nat.zero_mul, Nat.zero_add,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]

theorem stepXmssR_built (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (t : Nat) (ht : t < 512) :
    stepXmssR pk mu sig t = stepForwardRow (pk, mu)
      ((buildSignerProgram .xmssPoseidon2).getD t .idle)
      (stepXmssR pk mu sig t).prevState
      (stepXmssCells pk mu sig ((buildSignerProgram .xmssPoseidon2).getD t .idle)
        (stepXmssR pk mu sig t).prevState) := by
  obtain ⟨op, state, hop, he⟩ := stepForwardRun_at (pk, mu) (stepXmssCells pk mu sig)
    (buildSignerProgram .xmssPoseidon2) stepForwardZero t _ (stepXmssR_at pk mu sig t ht)
  rw [List.getD_eq_getElem?_getD, hop, Option.getD_some, he]
  rfl

theorem stepXmssR_sem (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (t : Nat) (op : StepOp) (ht : t + 1 < 512)
    (hop : (buildSignerProgram .xmssPoseidon2).getD t .idle = op)
    (hc : StepXmssChecks pk mu sig op (stepXmssR pk mu sig t).prevState) :
    StepRowSem (pk, mu) (stepXmssR pk mu sig) op t := by
  have hb := stepXmssR_built pk mu sig t (by omega)
  rw [hop] at hb
  have hgA := stepXmssRows_groupA pk mu sig _ (List.mem_of_getElem? (stepXmssR_at pk mu sig t (by omega)))
  have hvalid := (buildSignerProgram_kind_mem_and_valid .xmssPoseidon2 t).2
  rw [hop] at hvalid
  have hsup : stepXmssSupported op = true := by
    have hlen : t < (buildSignerProgram .xmssPoseidon2).length := by
      rw [buildSignerProgram_length.2.2.1]; omega
    have he : (buildSignerProgram .xmssPoseidon2)[t] = op := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] using hop
    exact List.all_eq_true.mp stepXmssProgram_supported op (he ▸ List.getElem_mem hlen)
  have hg := stepXmss_seed_guards_of_checks pk mu sig op _ hsup hc
  have hcon : allZeroGoldilocks (stepOpConstraints (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs (pk, mu) (stepXmssR pk mu sig t))) = true := by
    rw [hb]
    exact (stepForwardRow_constraints_iff _ _ _ _ hvalid).mpr hg
  have hparts := (stepOpConstraints_iff_guard_and_next _ _ _ hvalid).mp hcon
  refine ⟨stepOp256_groupA_exact _ hgA, hparts.1, ?_⟩
  intro j hj
  have hshift := stepForwardRun_shift (pk, mu) (stepXmssCells pk mu sig)
    (buildSignerProgram .xmssPoseidon2) stepForwardZero t _ _
    (stepXmssR_at pk mu sig t (by omega)) (stepXmssR_at pk mu sig (t + 1) ht)
  unfold stepPrev
  rw [← hshift]
  exact hparts.2 j hj

/-- Native acceptance gives one bounded leaf and one layer verifying to the public root. -/
theorem stepXmssNative_layer (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) :
    ∃ ls : WotsLayerSig, sig.layers = [ls] ∧ sig.statefulLeafIdx < 64 ∧
      verifyWotsLayer xmssPoseidon2Geom pk 0 0 sig.statefulLeafIdx
        (computeHmsgStateful pk sig.rRand (computeMessageMu pk msg) sig.statefulLeafIdx ls.tswCtr)
        ls = some pk.pkRoot := by
  simp only [verifyAggNativeSig.public_eqs] at h
  split at h
  · contradiction
  · rename_i hc
    have hfalse := Bool.eq_false_iff.mpr hc
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hfalse
    have hlen : sig.layers.length = 1 := by
      simpa only [xmssPoseidon2Geom.public_eqs] using hfalse.2
    cases hl : sig.layers with
    | nil => simp [hl] at hlen
    | cons ls tail =>
      have ht : tail = [] := by
        have htail : tail.length = 0 := by
          have hh := hlen
          rw [hl, List.length_cons] at hh
          omega
        exact List.eq_nil_of_length_eq_zero htail
      subst tail
      simp only [hl] at h
      have hF0 : xmssPoseidon2Geom.forsTrees = 0 := by simp only [xmssPoseidon2Geom.public_eqs]
      simp only [hF0, beq_self_eq_true, ↓reduceIte] at h
      change verifyAggNativeSigStateful xmssPoseidon2Geom pk (computeMessageMu pk msg) sig ls [] = true at h
      have hNL : xmssPoseidon2Geom.numLayers = 1 := by simp only [xmssPoseidon2Geom.public_eqs]
      have hSH : xmssPoseidon2Geom.subtreeHeight = 6 := by simp only [xmssPoseidon2Geom.public_eqs]
      simp only [verifyAggNativeSigStateful.public_eqs, hNL, hSH, Nat.reduceMul,
        Nat.reducePow, verifyUpperLayers_nil] at h
      split at h
      · contradiction
      · rename_i hc'
        have hf := Bool.eq_false_iff.mpr hc'
        simp only [Bool.or_eq_false_iff] at hf
        have hleaf : sig.statefulLeafIdx < 64 := by
          have hh := hf.2
          change (!decide (sig.statefulLeafIdx < 64)) = false at hh
          by_cases hb : sig.statefulLeafIdx < 64
          · exact hb
          · simp [hb] at hh
        have hd : sig.statefulLeafIdx / 64 = 0 := Nat.div_eq_of_lt hleaf
        have hm : sig.statefulLeafIdx % 64 = sig.statefulLeafIdx := Nat.mod_eq_of_lt hleaf
        rw [hd, hm] at h
        cases hr : verifyWotsLayer xmssPoseidon2Geom pk 0 0 sig.statefulLeafIdx
            (computeHmsgStateful pk sig.rRand (computeMessageMu pk msg) sig.statefulLeafIdx ls.tswCtr) ls with
        | none => simp only [hr, Bool.false_eq_true] at h
        | some root =>
          simp only [hr] at h
          have he : root = pk.pkRoot := beq_iff_eq.mp h
          exact ⟨ls, rfl, hleaf, he ▸ hr⟩


/-- Reconstruction without invoking the classical modular-arithmetic lemmas. -/
theorem stepForwardWeighted_digits (B w : Nat) (f : Nat → Goldilocks)
    (hB : B ≤ goldilocksPrime) (hB0 : 0 < B) :
    ∀ n, (∀ i < n, f i = Goldilocks.ofNat ((w / B ^ i) % B)) →
      stepWeightedNat f (fun i => B ^ i) n + B ^ n * (w / B ^ n) = w
  | 0, _ => by
    rw [Nat.pow_zero, Nat.div_one, Nat.one_mul]
    exact Nat.zero_add w
  | n + 1, h => by
    have ih := stepForwardWeighted_digits B w f hB hB0 n (fun i hi => h i (by omega))
    have hd : (w / B ^ n) % B < goldilocksPrime :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ hB0) hB
    have hq := Nat.div_add_mod (w / B ^ n) B
    have key : w / B ^ n % B * B ^ n + B ^ n * B * (w / B ^ n / B) = B ^ n * (w / B ^ n) := by
      rw [Nat.mul_comm (w / B ^ n % B) (B ^ n), Nat.mul_assoc, ← Nat.mul_add, Nat.add_comm, hq]
    rw [stepWeightedNat_succ, h n (by omega), Goldilocks.ofNat_val, Nat.mod_eq_of_lt hd,
      Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.add_assoc, key]
    exact ih

theorem stepForwardWeighted_bits (w n : Nat) (f : Nat → Goldilocks)
    (hf : ∀ i < n, f i = Goldilocks.ofNat ((w / 2 ^ i) % 2)) :
    stepWeightedSum f (fun i => 2 ^ i) n = Goldilocks.ofNat (w % 2 ^ n) := by
  have he := stepForwardWeighted_digits 2 w f (by decide) (by decide) n hf
  have hb : stepWeightedNat f (fun i => 2 ^ i) n < 2 ^ n :=
    stepWeightedNat_bits_lt f n (fun i hi => by
      rw [hf i hi]
      have hm : w / 2 ^ i % 2 = 0 ∨ w / 2 ^ i % 2 = 1 := by omega
      rcases hm with hm | hm
      · exact Or.inl (by rw [hm]; rfl)
      · exact Or.inr (by rw [hm]; rfl))
  have hdiv := Nat.mod_add_div w (2 ^ n)
  rw [stepWeightedSum_eq_ofNat]
  congr 1
  omega

theorem stepXmssR_aux (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (t i : Nat) (ht : t < 512) (hi : i < 38) (op : StepOp)
    (hop : (buildSignerProgram .xmssPoseidon2).getD t .idle = op) :
    stepAux (stepXmssR pk mu sig) t i =
      stepXmssAux sig op (stepXmssR pk mu sig t).prevState i := by
  have he := congrArg (fun r : StepOpRow => r.aux.getD i Goldilocks.zero)
    (stepXmssR_built pk mu sig t ht)
  rw [hop] at he
  exact he.trans (stepXmssSeedRow_aux pk mu sig op _ i hi)

/-- The randomizer is retained exactly by construction, without an acceptance premise. -/
theorem stepXmssRows_randomizer (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    (stepXmssSig (stepOpSlotRow .xmssPoseidon2 (stepXmssRows pk mu sig) 0)).rRand = sig.rRand := by
  change stepAuxLane (stepXmssR pk mu sig) 1 0 = sig.rRand
  have ha : ∀ i < 4, stepAux (stepXmssR pk mu sig) 1 i =
      sig.rRand.toList.getD i Goldilocks.zero := by
    intro i hi
    have h := stepXmssR_aux pk mu sig 1 i (by decide) (by omega)
      .statefulHmsgBlock1 stepXmssProgram_at_1
    simpa only [stepXmssAux] using h
  apply Lane4.ext
  · simpa only [stepAuxLane, Lane4.toList_eq, List.getD_cons_zero] using ha 0 (by decide)
  · simpa only [stepAuxLane, Nat.reduceAdd, Lane4.toList_eq,
      List.getD_cons_succ, List.getD_cons_zero] using ha 1 (by decide)
  · simpa only [stepAuxLane, Nat.reduceAdd, Lane4.toList_eq,
      List.getD_cons_succ, List.getD_cons_zero] using ha 2 (by decide)
  · simpa only [stepAuxLane, Nat.reduceAdd, Lane4.toList_eq,
      List.getD_cons_succ, List.getD_cons_zero] using ha 3 (by decide)

/-- The first three interpreter instructions compute precisely native stateful Hmsg. -/
theorem stepXmssR_hmsg (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (ls : WotsLayerSig) (hlayers : sig.layers = [ls]) (hleaf : sig.statefulLeafIdx < 64) :
    stepHmsgOf (stepRegsAt (stepXmssR pk mu sig) 3).main =
      computeHmsgStateful pk sig.rRand mu sig.statefulLeafIdx ls.tswCtr ∧
    (∀ s < 6, (stepRegsAt (stepXmssR pk mu sig) 3).rem.get s = Goldilocks.zero) ∧
    (stepRegsAt (stepXmssR pk mu sig) 3).acc = Goldilocks.zero ∧
    StepAddrOk (stepRegsAt (stepXmssR pk mu sig) 3) sig.statefulLeafIdx 0 := by
  let R := stepXmssR pk mu sig
  have h0 := stepXmssR_sem pk mu sig 0 .statefulHmsgBlock0 (by decide) stepXmssProgram_at_0 True.intro
  have h1 := stepXmssR_sem pk mu sig 1 .statefulHmsgBlock1 (by decide) stepXmssProgram_at_1 True.intro
  have h2 := stepXmssR_sem pk mu sig 2 .statefulHmsgSqueeze (by decide) stepXmssProgram_at_2 True.intro
  obtain ⟨_, _, hin0, hr1⟩ := stepSem_statefulHmsgBlock0 h0
  obtain ⟨hin1, hr2⟩ := stepSem_statefulHmsgBlock1 h1
  obtain ⟨hin2, hr3⟩ := stepSem_statefulHmsgSqueeze h2
  have hb6 : stepWeightedSum (stepAux R 0) (fun i => 2 ^ i) 6 = Goldilocks.ofNat sig.statefulLeafIdx := by
    have hh := stepForwardWeighted_bits sig.statefulLeafIdx 6 (stepAux R 0) (fun i hi => by
      rw [stepXmssR_aux pk mu sig 0 i (by decide) (by omega) .statefulHmsgBlock0 stepXmssProgram_at_0]
      simp only [stepXmssAux, hi, ↓reduceIte])
    simpa only [Nat.mod_eq_of_lt hleaf] using hh
  have hb32 : stepWeightedSum (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32 =
      Goldilocks.ofNat (ls.tswCtr % 2 ^ 32) := by
    apply stepForwardWeighted_bits
    intro i hi
    rw [stepXmssR_aux pk mu sig 0 (6 + i) (by decide) (by omega) .statefulHmsgBlock0 stepXmssProgram_at_0]
    simp only [stepXmssAux, hlayers, List.getD_cons_zero,
      show ¬6 + i < 6 by omega, show 6 + i < 38 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  have hin0' : (R 0).stIn = hmsgStatefulIn0 pk mu sig.statefulLeafIdx ls.tswCtr := by
    rw [hin0, hb6, hb32]
    simp only [hmsgStatefulIn0.public_eqs]
    rw [Nat.mod_eq_of_lt (show sig.statefulLeafIdx < 2 ^ 32 by omega), g_ofNat_add, g_ofNat_mul]
  have hrand : stepAuxLane R 1 0 = sig.rRand := stepXmssRows_randomizer pk mu sig
  have main1 : (stepRegsAt R 1).main = poseidon2Perm12 (hmsgStatefulIn0 pk mu sig.statefulLeafIdx ls.tswCtr) := by
    rw [hr1]
    change poseidon2Perm12 (R 0).stIn = _
    rw [hin0']
  have hin1' : (R 1).stIn = hmsgStatefulIn1
      (poseidon2Perm12 (hmsgStatefulIn0 pk mu sig.statefulLeafIdx ls.tswCtr)) sig.rRand mu := by
    rw [hin1, main1, hrand]
    simp only [hmsgStatefulIn1.public_eqs]
  have main2 : (stepRegsAt R 2).main = poseidon2Perm12 (R 1).stIn := by rw [hr2]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr3]
    change stepHmsgOf (poseidon2Perm12 (R 2).stIn) = _
    rw [hin2]
    unfold stepSqueezeIn
    rw [main2, hin1', computeHmsgStateful_eq_states]
    simp only [state12OutDigest5.public_eqs, spongePadOne.public_eqs, stepHmsgOf]
  · intro s hs
    rw [hr3]
    rcases s with _ | _ | _ | _ | _ | _ | s <;> first | rfl | omega
  · rw [hr3]
  · constructor
    · rw [hr3, hr2, hr1]
      exact hb6
    · rw [hr3, hr2, hr1]
      rfl
    · rw [hr3, hr2, hr1]
      rfl


/-- The native layer checks the canonical digest digits and their target sum. -/
theorem stepXmssNative_digits (pk : AggValidatorPk) (d : Digest5) (ls : WotsLayerSig)
    (leaf : Nat) (h : verifyWotsLayer xmssPoseidon2Geom pk 0 0 leaf d ls = some pk.pkRoot) :
    checkDigest5Limbs63 d = true ∧
    listNatSum ((List.range' 0 128).map (stepDigit d)) = 192 ∧
    ls.wotsChains.length = 128 ∧ ls.merklePath.length = 6 := by
  simp only [verifyWotsLayer.public_eqs] at h
  split at h
  · rename_i hlen
    simp only [Bool.and_eq_true, beq_iff_eq] at hlen
    cases he : extractWotsDigitsChecked xmssPoseidon2Geom d with
    | none => simp [he] at h
    | some ds =>
      simp only [he] at h
      split at h
      · rename_i hsum
        have hchk : checkDigest5Limbs63 d = true := by
          simp only [extractWotsDigitsChecked.public_eqs] at he
          split at he
          · assumption
          · contradiction
        have hd := stepDigits_extract xmssPoseidon2Geom d (by simp only [xmssPoseidon2Geom.public_eqs]) hchk
        rw [he] at hd
        have hd' : ds = (List.range' 0 128).map (stepDigit d) := Option.some.inj hd
        have hsum' : listNatSum ds = 192 := by
          simpa only [xmssPoseidon2Geom.public_eqs] using beq_iff_eq.mp hsum
        exact ⟨hchk, hd' ▸ hsum',
          by simpa only [xmssPoseidon2Geom.public_eqs] using hlen.1,
          by simpa only [xmssPoseidon2Geom.public_eqs] using hlen.2⟩
      · contradiction
  · contradiction



/-- A digest range check bounds each decomposition source register. -/

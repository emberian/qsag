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
theorem stepForward_digest_limb (prev : List Goldilocks) (l : Nat) (hl : l < 5)
    (h : checkDigest5Limbs63 (stepHmsgOf (stepRegs (fun j => prev.getD j Goldilocks.zero)).main) = true) :
    (prev.getD (stMainSponge + l) Goldilocks.zero).val < 2 ^ 63 := by
  simp only [checkDigest5Limbs63.public_eqs, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases l with _ | _ | _ | _ | _ | l
  · exact h.1.1.1.1
  · exact h.1.1.1.2
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2
  · omega

/-- The computed accumulator adds exactly this limb's native digits, independently of guards. -/
theorem stepXmss_decomp_acc_expected (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (l : Nat) (hl : l < 5) :
    stepHmsgDecompExpected (stepOpRowInputs (pk, mu)
      (stepXmssSeedRow pk mu sig (.hmsgDecompLimb l) prev)) l stAccOrU1 =
    prev.getD stAccOrU1 Goldilocks.zero +ₚ Goldilocks.ofNat
      (listNatSum ((List.range' (31 * l) (stepLimbDigits l)).map
        (stepDigit (stepHmsgOf (stepRegs (fun j => prev.getD j Goldilocks.zero)).main)))) := by
  let x := stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.hmsgDecompLimb l) prev)
  let d := stepHmsgOf (stepRegs (fun j => prev.getD j Goldilocks.zero)).main
  have hlimb : digest5Limb d l = prev.getD (stMainSponge + l) Goldilocks.zero := by
    rcases l with _ | _ | _ | _ | _ | l <;> first | rfl | omega
  have hn : stepLimbDigits l ≤ 31 := by unfold stepLimbDigits; split <;> omega
  have hd : ∀ i ∈ List.range (stepLimbDigits l), x.aux i = Goldilocks.ofNat (stepDigit d (31 * l + i)) := by
    intro i hi
    have hi' := List.mem_range.mp hi
    have hi31 : i < 31 := by omega
    rw [stepXmssSeedRow_aux pk mu sig _ prev i (by omega)]
    simp only [stepXmssAux, hi31, ↓reduceIte]
    unfold stepDigit
    rw [show (31 * l + i) / 31 = l by omega, show (31 * l + i) % 31 = i by omega, hlimb]
  have he := stepPlainSum_field x (stepDigit d) l (List.range (stepLimbDigits l)) 0 hd
  change stepHmsgDecompExpected x l stAccOrU1 = _
  rw [stepHmsgDecompExpected.public_eqs, ite_eq_left rfl]
  change x.prev stAccOrU1 +ₚ stepPlainSum x.aux (stepLimbDigits l) = _
  simp only [stepPlainSum.public_eqs]
  have hz : Goldilocks.ofNat 0 = Goldilocks.zero := rfl
  rw [hz] at he
  rw [he, Nat.zero_add, range'_eq_map, List.map_map]
  rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- Native digit checks establish the full five-row decomposition segment. -/
theorem stepXmssR_decomp (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (hchk : checkDigest5Limbs63 (stepHmsgOf (stepRegsAt (stepXmssR pk mu sig) 3).main) = true)
    (hsum : listNatSum ((List.range' 0 128).map
      (stepDigit (stepHmsgOf (stepRegsAt (stepXmssR pk mu sig) 3).main))) = 192)
    (hacc : (stepRegsAt (stepXmssR pk mu sig) 3).acc = Goldilocks.zero) :
    StepRunAt (pk, mu) (stepXmssR pk mu sig) ((List.range 5).map StepOp.hmsgDecompLimb) 3 := by
  let R := stepXmssR pk mu sig
  let d := stepHmsgOf (stepRegsAt R 3).main
  have hp : ∀ l, l ≤ 4 →
      (stepRegsAt R (3 + l)).main = (stepRegsAt R 3).main ∧
      (stepRegsAt R (3 + l)).acc = Goldilocks.ofNat
        (listNatSum ((List.range' 0 (31 * l)).map (stepDigit d))) ∧
      ∀ j < l, StepRowSem (pk, mu) R (.hmsgDecompLimb j) (3 + j) := by
    intro l
    induction l with
    | zero =>
      intro _
      exact ⟨rfl, by simpa only [Nat.mul_zero, List.range'_zero, List.map_nil,
        listNatSum.public_eqs, Nat.add_zero, R,
        show Goldilocks.ofNat 0 = Goldilocks.zero from rfl] using hacc, fun j hj => False.elim (by omega)⟩
    | succ l ih =>
      intro hl
      obtain ⟨hm, ha, hrun⟩ := ih (by omega)
      have hlt : ((R (3 + l)).prevState.getD (stMainSponge + l) Goldilocks.zero).val < 2 ^ 63 := by
        apply stepForward_digest_limb _ l (by omega)
        change checkDigest5Limbs63 (stepHmsgOf (stepRegsAt R (3 + l)).main) = true
        rw [hm]
        exact hchk
      have hsem := stepXmssR_sem pk mu sig (3 + l) (.hmsgDecompLimb l) (by omega)
        (stepXmssProgram_decomp l (by omega)) ⟨hlt, fun he => False.elim (by omega)⟩
      obtain ⟨_, _, hacc', _, hf⟩ := stepDecomp_row (by omega : l < 5) hsem
        (fun s => ((stepRegsAt R (3 + l)).rem.get s).val)
        (listNatSum ((List.range' 0 (31 * l)).map (stepDigit d)))
        (fun s _ => (g_ofNat_self _).symm) ha
      have hn : stepLimbDigits l = 31 := by simp [stepLimbDigits, show l < 4 by omega]
      rw [hm, hn] at hacc'
      refine ⟨?_, ?_, ?_⟩
      · have he : 3 + (l + 1) = 3 + l + 1 := by omega
        rw [he, hf]
        exact hm
      · have he : 3 + (l + 1) = 3 + l + 1 := by omega
        rw [he, hacc']
        apply congrArg Goldilocks.ofNat
        rw [show 31 * (l + 1) = 31 * l + 31 by omega,
          range'_split, Nat.zero_add, List.map_append, listNatSum_append]
      · intro j hj
        by_cases he : j = l
        · subst j; exact hsem
        · exact hrun j (by omega)
  obtain ⟨hm4, ha4, hrun4⟩ := hp 4 (by decide)
  have hlt4 : ((R 7).prevState.getD (stMainSponge + 4) Goldilocks.zero).val < 2 ^ 63 := by
    apply stepForward_digest_limb _ 4 (by decide)
    change checkDigest5Limbs63 (stepHmsgOf (stepRegsAt R 7).main) = true
    rw [hm4]
    exact hchk
  have he4 : stepHmsgDecompExpected (stepOpRowInputs (pk, mu)
      (stepXmssSeedRow pk mu sig (.hmsgDecompLimb 4) (R 7).prevState)) 4 stAccOrU1 = Goldilocks.ofNat 192 := by
    rw [stepXmss_decomp_acc_expected pk mu sig _ 4 (by decide)]
    change (stepRegsAt R 7).acc +ₚ Goldilocks.ofNat
      (listNatSum ((List.range' 124 4).map (stepDigit (stepHmsgOf (stepRegsAt R 7).main)))) = _
    rw [ha4, hm4, ← g_ofNat_add]
    have he : List.range' 0 128 = List.range' 0 124 ++ List.range' 124 4 := by
      exact range'_split 124 0 4
    rw [he, List.map_append, listNatSum_append] at hsum
    exact congrArg Goldilocks.ofNat hsum
  have hsem4 := stepXmssR_sem pk mu sig 7 (.hmsgDecompLimb 4) (by decide) (stepXmssProgram_decomp 4 (by decide)) ⟨hlt4, fun _ => he4⟩
  intro i hi
  have hi5 : i < 5 := by simpa only [List.length_map, List.length_range] using hi
  simp only [List.getElem_map, List.getElem_range]
  by_cases he : i = 4
  · subst i; exact hsem4
  · exact hrun4 i (by omega)


/-- Natural-number model of the remaining-count registers after consuming `c` chains. -/
def stepForwardRemNat (v : Nat → Nat) : Nat → Nat → Nat
  | 0, s => v s
  | c + 1, s => if s = wotsPackSlot c then stepForwardRemNat v c s / 4 else stepForwardRemNat v c s

theorem stepForwardRemNat_le (v : Nat → Nat) (c s : Nat) : stepForwardRemNat v c s ≤ v s := by
  induction c with
  | zero => exact Nat.le_refl _
  | succ c ih =>
    unfold stepForwardRemNat
    split
    · exact Nat.le_trans (Nat.div_le_self _ _) ih
    · exact ih

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepForwardRemNat_end (v : Nat → Nat)
    (hv : ∀ s < 5, v s < 4 ^ (if s < 3 then 26 else 25)) :
    ∀ s < 5, stepForwardRemNat v 128 s = 0 := by
  intro s hs
  have hbound := hv s hs
  rcases s with _ | _ | _ | _ | _ | s
  all_goals first | omega | skip
  all_goals simp only [stepForwardRemNat, wotsPackSlot.public_eqs, Nat.reduceLT, Nat.reduceEqDiff,
    ↓reduceIte, Nat.div_div_eq_div_mul]
  all_goals exact Nat.div_eq_of_lt hbound

theorem stepForwardRegs_rem (prev : List Goldilocks) (s : Nat) (hs : s < 6) :
    (stepRegs (fun j => prev.getD j Goldilocks.zero)).rem.get s =
      prev.getD (stRemPack + s) Goldilocks.zero := by
  rcases s with _ | _ | _ | _ | _ | _ | s <;> first | rfl | omega

/-- One constructed chain consumes precisely one base-4 quotient, without needing its digit invariant. -/
theorem stepXmssR_chain_rem (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (t c : Nat) (odd : Bool) (ht : t + 3 < 512)
    (h0 : (buildSignerProgram .xmssPoseidon2).getD t .idle = .wotsChainStep0 0 c (wotsPackSlot c))
    (h1 : (buildSignerProgram .xmssPoseidon2).getD (t + 1) .idle = .wotsChainStep1 0 c)
    (h2 : (buildSignerProgram .xmssPoseidon2).getD (t + 2) .idle = .wotsChainStep2 0 c odd) :
    (stepRegsAt (stepXmssR pk mu sig) (t + 3)).rem =
      (stepRegsAt (stepXmssR pk mu sig) t).rem.set (wotsPackSlot c)
        (Goldilocks.ofNat (((stepRegsAt (stepXmssR pk mu sig) t).rem.get (wotsPackSlot c)).val / 4)) := by
  let R := stepXmssR pk mu sig
  have hs : wotsPackSlot c < 6 := Nat.lt_succ_of_lt (wotsPackSlot_lt_5 c)
  have hsem0 := stepXmssR_sem pk mu sig t _ (by omega) h0 True.intro
  have hsem1 := stepXmssR_sem pk mu sig (t + 1) _ (by omega) h1 True.intro
  have hsem2 := stepXmssR_sem pk mu sig (t + 2) _ (by omega) h2 (by cases odd <;> exact True.intro)
  have hr1 := (stepSem_wotsChainStep0 hs hsem0).2.2.2.2.2.2.2
  have hr2 : stepRegsAt R (t + 2) = _ := (stepSem_wotsChainStep1 hsem1).2
  have hr3 : (stepRegsAt R (t + 3)).rem = (stepRegsAt R (t + 2)).rem := by
    cases odd
    · have he : stepRegsAt R (t + 3) = _ := (stepSem_wotsChainStep2_even hsem2).2
      rw [he]
    · have he : stepRegsAt R (t + 3) = _ := (stepSem_wotsChainStep2_odd hsem2).2
      rw [he]
  rw [hr3, hr2, hr1]
  have ha := stepXmssR_aux pk mu sig t 7 (by omega) (by decide) _ h0
  change stepAux R t 7 = _ at ha
  rw [ha]
  change (stepRegsAt R t).rem.set (wotsPackSlot c)
      (Goldilocks.ofNat (((R t).prevState.getD (stRemPack + wotsPackSlot c) Goldilocks.zero).val / 4)) = _
  have hget : (stepRegsAt R t).rem.get (wotsPackSlot c) =
      (R t).prevState.getD (stRemPack + wotsPackSlot c) Goldilocks.zero :=
    stepForwardRegs_rem _ _ hs
  rw [hget]

/-- Updating a quotient register agrees with the natural-number consumption model. -/
theorem stepForwardRemNat_step (v : Nat → Nat) (r : StepRem) (c : Nat)
    (hr : ∀ s < 5, r.get s = Goldilocks.ofNat (stepForwardRemNat v c s))
    (hv : ∀ s < 5, v s < goldilocksPrime) :
    ∀ s < 5, (r.set (wotsPackSlot c) (Goldilocks.ofNat ((r.get (wotsPackSlot c)).val / 4))).get s =
      Goldilocks.ofNat (stepForwardRemNat v (c + 1) s) := by
  intro s hs
  rw [StepRem.get_set _ _ _ _ (Nat.lt_succ_of_lt (wotsPackSlot_lt_5 c))]
  unfold stepForwardRemNat
  by_cases he : s = wotsPackSlot c
  · rw [ite_eq_left he, ite_eq_left he, ← he, hr s hs, Goldilocks.ofNat_val,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (stepForwardRemNat_le v c s) (hv s hs))]
  · rw [ite_eq_right he, ite_eq_right he]
    exact hr s hs


/-- Packed native remaining counts fit the five register capacities. -/
theorem stepForward_pack_bounds (d : Digest5) (r : StepRem)
    (hpack : ∀ s < 6, r.get s = Goldilocks.ofNat
      (stepPackFold (stepDigit d) s (List.range' 0 128) 0)) :
    ∀ s < 5, (r.get s).val < 4 ^ (if s < 3 then 26 else 25) := by
  intro s hs
  rcases s with _ | _ | _ | _ | _ | s
  · have he := hpack 0 (by decide)
    rw [stepPackFold_slot _ 0 0 26 wotsPackSlot_range0 (by decide) (by simp only [wotsPackSlotStart.public_eqs])] at he
    have hb := evalBaseDigits_lt_pow 4 (by decide)
      ((List.range' 0 26).map (fun c => 3 - stepDigit d c)) (fun x hx => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        omega)
    rw [List.length_map, List.length_range'] at hb
    rw [he, Goldilocks.ofNat_val, Nat.mod_eq_of_lt
      (Nat.lt_trans hb (by decide : 4 ^ 26 < goldilocksPrime))]
    exact hb
  · have he := hpack 1 (by decide)
    rw [stepPackFold_slot _ 1 26 26 wotsPackSlot_range1 (by decide) (by simp only [wotsPackSlotStart.public_eqs])] at he
    have hb := evalBaseDigits_lt_pow 4 (by decide)
      ((List.range' 26 26).map (fun c => 3 - stepDigit d c)) (fun x hx => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        omega)
    rw [List.length_map, List.length_range'] at hb
    rw [he, Goldilocks.ofNat_val, Nat.mod_eq_of_lt
      (Nat.lt_trans hb (by decide : 4 ^ 26 < goldilocksPrime))]
    exact hb
  · have he := hpack 2 (by decide)
    rw [stepPackFold_slot _ 2 52 26 wotsPackSlot_range2 (by decide) (by simp only [wotsPackSlotStart.public_eqs])] at he
    have hb := evalBaseDigits_lt_pow 4 (by decide)
      ((List.range' 52 26).map (fun c => 3 - stepDigit d c)) (fun x hx => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        omega)
    rw [List.length_map, List.length_range'] at hb
    rw [he, Goldilocks.ofNat_val, Nat.mod_eq_of_lt
      (Nat.lt_trans hb (by decide : 4 ^ 26 < goldilocksPrime))]
    exact hb
  · have he := hpack 3 (by decide)
    rw [stepPackFold_slot _ 3 78 25 wotsPackSlot_range3 (by decide) (by simp only [wotsPackSlotStart.public_eqs])] at he
    have hb := evalBaseDigits_lt_pow 4 (by decide)
      ((List.range' 78 25).map (fun c => 3 - stepDigit d c)) (fun x hx => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        omega)
    rw [List.length_map, List.length_range'] at hb
    rw [he, Goldilocks.ofNat_val, Nat.mod_eq_of_lt
      (Nat.lt_trans hb (by decide : 4 ^ 25 < goldilocksPrime))]
    exact hb
  · have he := hpack 4 (by decide)
    rw [stepPackFold_slot _ 4 103 25 wotsPackSlot_range4 (by decide) (by simp only [wotsPackSlotStart.public_eqs])] at he
    have hb := evalBaseDigits_lt_pow 4 (by decide)
      ((List.range' 103 25).map (fun c => 3 - stepDigit d c)) (fun x hx => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        omega)
    rw [List.length_map, List.length_range'] at hb
    rw [he, Goldilocks.ofNat_val, Nat.mod_eq_of_lt
      (Nat.lt_trans hb (by decide : 4 ^ 25 < goldilocksPrime))]
    exact hb
  · omega

/-- Glue verified instruction segments without assuming a valid table. -/
theorem stepForwardRunAt_append (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (a b : List StepOp) (t : Nat) (ha : StepRunAt pub R a t)
    (hb : StepRunAt pub R b (t + a.length)) : StepRunAt pub R (a ++ b) t := by
  intro i hi
  by_cases hia : i < a.length
  · rw [List.getElem_append_left hia]
    exact ha i hia
  · have hib : i - a.length < b.length := by rw [List.length_append] at hi; omega
    rw [List.getElem_append_right (Nat.le_of_not_lt hia)]
    have he := hb (i - a.length) hib
    have ht : t + a.length + (i - a.length) = t + i := by omega
    rw [ht] at he
    exact he

theorem stepForwardRunAt_pairs (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (layer t n : Nat) (h : ∀ p < n, StepRunAt pub R (stepPairOps layer p) (t + 7 * p)) :
    StepRunAt pub R ((List.range n).flatMap (stepPairOps layer)) t := by
  induction n with
  | zero => intro i hi; simp at hi
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply stepForwardRunAt_append
    · exact ih (fun p hp => h p (by omega))
    · have hl : ((List.range n).flatMap (stepPairOps layer)).length = 7 * n :=
        by rw [flatMap_range_uniform_length _ 7 (fun _ => rfl)]; omega
      rw [hl]
      exact h n (by omega)

theorem stepXmssR_pair_run (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (p : Nat) (hp : p < 64)
    (hcheck : p + 1 = 64 → ∀ s < 5,
      (stepXmssR pk mu sig (9 + 7 * p + 6)).prevState.getD (stRemPack + s) Goldilocks.zero =
        Goldilocks.zero) :
    StepRunAt (pk, mu) (stepXmssR pk mu sig) (stepPairOps 0 p) (9 + 7 * p) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := stepXmssProgram_pairs p hp
  intro i hi
  change i < 7 at hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | i
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h0 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h1 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h2 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h3 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h4 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h5 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h6 hcheck
  · exact False.elim (by omega)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- The constructed WOTS segment exhausts the packed counts and satisfies every row guard. -/
theorem stepXmssR_wots (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (hbound : ∀ s < 5, ((stepRegsAt (stepXmssR pk mu sig) 8).rem.get s).val <
      4 ^ (if s < 3 then 26 else 25)) :
    StepRunAt (pk, mu) (stepXmssR pk mu sig) (stepWotsOps 0) 8 := by
  let R := stepXmssR pk mu sig
  let v := fun s => ((stepRegsAt R 8).rem.get s).val
  have hv : ∀ s < 5, v s < goldilocksPrime := fun s _ => ((stepRegsAt R 8).rem.get s).isLt
  have hinit := stepXmssR_sem pk mu sig 8 (.wotsTellInit 0) (by decide) stepXmssProgram_at_8 True.intro
  have hr9 := (stepSem_wotsTellInit hinit).2
  have hpref : ∀ p, p ≤ 64 →
      (∀ s < 5, (stepRegsAt R (9 + 7 * p)).rem.get s = Goldilocks.ofNat (stepForwardRemNat v (2 * p) s)) ∧
      (∀ q < p, StepRunAt (pk, mu) R (stepPairOps 0 q) (9 + 7 * q)) := by
    intro p
    induction p with
    | zero =>
      intro _
      constructor
      · intro s _
        change (stepRegsAt R 9).rem.get s = Goldilocks.ofNat (v s)
        rw [hr9]
        exact (g_ofNat_self _).symm
      · intro q hq; exact False.elim (by omega)
    | succ p ih =>
      intro hp
      obtain ⟨hm, hrun⟩ := ih (by omega)
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := stepXmssProgram_pairs p (by omega)
      have he := stepXmssR_chain_rem pk mu sig (9 + 7 * p) (2 * p) false (by omega) h0 h1 h2
      have ho := stepXmssR_chain_rem pk mu sig (9 + 7 * p + 3) (2 * p + 1) true (by omega) h3
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using h4)
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using h5)
      have hm3 : ∀ s < 5, (stepRegsAt R (9 + 7 * p + 3)).rem.get s =
          Goldilocks.ofNat (stepForwardRemNat v (2 * p + 1) s) := by
        intro s hs
        rw [he]
        exact stepForwardRemNat_step v _ (2 * p) hm hv s hs
      have hm6 : ∀ s < 5, (stepRegsAt R (9 + 7 * p + 6)).rem.get s =
          Goldilocks.ofNat (stepForwardRemNat v (2 * p + 2) s) := by
        intro s hs
        have ho' : (stepRegsAt R (9 + 7 * p + 6)).rem = _ := ho
        rw [ho']
        exact stepForwardRemNat_step v _ (2 * p + 1) hm3 hv s hs
      have hc : p + 1 = 64 → ∀ s < 5,
          (R (9 + 7 * p + 6)).prevState.getD (stRemPack + s) Goldilocks.zero = Goldilocks.zero := by
        intro hlast s hs
        have hget : (stepRegsAt R (9 + 7 * p + 6)).rem.get s =
            (R (9 + 7 * p + 6)).prevState.getD (stRemPack + s) Goldilocks.zero :=
          stepForwardRegs_rem _ _ (by omega)
        rw [← hget, hm6 s hs, show 2 * p + 2 = 128 by omega,
          stepForwardRemNat_end v hbound s hs]
        rfl
      have hpair := stepXmssR_pair_run pk mu sig p (by omega) hc
      have habs : StepRowSem (pk, mu) R (.wotsTellPairAbsorb p) (9 + 7 * p + 6) :=
        hpair 6 (by change 6 < 7; decide)
      have hnext : stepRegsAt R (9 + 7 * p + 7) = _ := (stepSem_wotsTellPairAbsorb habs).2.2
      constructor
      · intro s hs
        rw [show 9 + 7 * (p + 1) = 9 + 7 * p + 7 by omega, hnext]
        exact hm6 s hs
      · intro q hq
        by_cases heq : q = p
        · subst q; exact hpair
        · exact hrun q (by omega)
  have hpairs := (hpref 64 (by decide)).2
  have hsqueeze := stepXmssR_sem pk mu sig 457 .wotsTellFinalSqueeze (by decide) stepXmssProgram_at_457 True.intro
  unfold stepWotsOps
  apply stepForwardRunAt_append
  · apply stepForwardRunAt_append
    · intro i hi
      have hi0 : i = 0 := by change i < 1 at hi; omega
      subst i; exact hinit
    · exact stepForwardRunAt_pairs (pk, mu) R 0 9 64 hpairs
  · have hl : ([StepOp.wotsTellInit 0] ++ (List.range 64).flatMap (stepPairOps 0)).length = 449 := by
      rw [List.length_append, flatMap_range_uniform_length _ 7 (fun _ => rfl)]
      rfl
    rw [hl]
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i; exact hsqueeze


set_option maxHeartbeats 1000000 in
/-- Layer computation without assuming the final root-comparison guard. -/
theorem stepLayer_verify_forward {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {geom : AggSigGeometry} {layer h tD kpN tree ctr : Nat}
    (hDec : StepRunAt pub R ((List.range 5).map StepOp.hmsgDecompLimb) tD)
    (hWots : StepRunAt pub R (stepWotsOps layer) (tD + 5))
    (hRem0 : ∀ s < 6, (stepRegsAt R tD).rem.get s = Goldilocks.zero)
    (hAcc0 : (stepRegsAt R tD).acc = Goldilocks.zero)
    (hAddr : StepAddrOk (stepRegsAt R tD) kpN tree)
    (hA : ∀ l < h, StepRowSem pub R (.xmssMerkleBlockA layer l) (tD + 455 + 2 * l))
    (hBin : ∀ l < h, (R (tD + 455 + 2 * l + 1)).stIn =
      stepMerkleBIn (stepRegsAt R (tD + 455 + 2 * l + 1)))
    (hBnext : ∀ l, l + 1 < h → stepRegsAt R (tD + 455 + 2 * l + 2) =
      { stepRegsAt R (tD + 455 + 2 * l + 1) with
        work := (stepPermAt R (tD + 455 + 2 * l + 1)).b0 })
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
  have e450 : tD + 5 + 450 = tD + 455 := by omega
  obtain ⟨hd, hSlots, hWork, hCur450R, hAddr450, hCursor⟩ :=
    stepWots_sem hWots hAddr5 hl hk
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


theorem stepXmssProgram_chains : ∀ c < 128,
    (buildSignerProgram .xmssPoseidon2).getD (stepChainRow 8 c) .idle =
      .wotsChainStep0 0 c (wotsPackSlot c) := by
  simpa only [stepChainRow] using buildSignerProgram_xmss_chains



theorem stepXmssR_chain_lane (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (ls : WotsLayerSig) (hlayers : sig.layers = [ls]) (c : Nat) (hc : c < 128) :
    stepAuxLane (stepXmssR pk mu sig) (stepChainRow 8 c) 0 = ls.wotsChains.getD c lane4Zero := by
  have ht : stepChainRow 8 c < 512 := by unfold stepChainRow; omega
  have hop := stepXmssProgram_chains c hc
  have ha : ∀ i < 4, stepAux (stepXmssR pk mu sig) (stepChainRow 8 c) i =
      (ls.wotsChains.getD c lane4Zero).toList.getD i Goldilocks.zero := by
    intro i hi
    rw [stepXmssR_aux pk mu sig _ i ht (by omega) _ hop]
    simp only [stepXmssAux, hlayers, List.getD_cons_zero, hi, ↓reduceIte]
  exact Lane4.ext (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) (ha 3 (by decide))

theorem stepXmssR_path_lane (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (ls : WotsLayerSig) (hlayers : sig.layers = [ls]) (l : Nat) (hl : l < 6) :
    stepAuxLane (stepXmssR pk mu sig) (458 + 2 * l) 2 = ls.merklePath.getD l lane4Zero := by
  have ht : 458 + 2 * l < 512 := by omega
  have hop := (stepXmssProgram_merkle l hl).1
  have ha : ∀ i < 4, stepAux (stepXmssR pk mu sig) (458 + 2 * l) (2 + i) =
      (ls.merklePath.getD l lane4Zero).toList.getD i Goldilocks.zero := by
    intro i hi
    rw [stepXmssR_aux pk mu sig _ (2 + i) ht (by omega) _ hop]
    simp only [stepXmssAux, hlayers, List.getD_cons_zero,
      show ¬2 + i = 0 by omega, show ¬2 + i = 1 by omega,
      show 2 + i < 6 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  exact Lane4.ext (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) (ha 3 (by decide))

theorem stepXmssR_chain_values (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (ls : WotsLayerSig) (hlayers : sig.layers = [ls]) (hlen : ls.wotsChains.length = 128) :
    stepLayerChains (stepXmssR pk mu sig) 8 = ls.wotsChains := by
  apply List.ext_getElem
  · simp only [stepLayerChains, List.length_map, List.length_range, hlen]
  · intro i hi hi'
    have hi128 : i < 128 := by simpa only [stepLayerChains, List.length_map, List.length_range] using hi
    simp only [stepLayerChains, List.getElem_map, List.getElem_range]
    rw [stepXmssR_chain_lane pk mu sig ls hlayers i hi128,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]

theorem stepXmssR_path_values (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (ls : WotsLayerSig) (hlayers : sig.layers = [ls]) (hlen : ls.merklePath.length = 6) :
    stepLayerPath (stepXmssR pk mu sig) 458 6 = ls.merklePath := by
  apply List.ext_getElem
  · simp only [stepLayerPath, List.length_map, List.length_range, hlen]
  · intro i hi hi'
    have hi6 : i < 6 := by simpa only [stepLayerPath, List.length_map, List.length_range] using hi
    simp only [stepLayerPath, List.getElem_map, List.getElem_range]
    rw [stepXmssR_path_lane pk mu sig ls hlayers i hi6,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]


/-- Every constructed Merkle A row already satisfies its guards. -/
theorem stepXmssR_merkleA (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (l : Nat) (hl : l < 6) :
    StepRowSem (pk, mu) (stepXmssR pk mu sig) (.xmssMerkleBlockA 0 l) (458 + 2 * l) :=
  stepXmssR_sem pk mu sig _ _ (by omega) (stepXmssProgram_merkle l hl).1 True.intro

theorem stepXmssR_merkleB (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (l : Nat) (hl : l < 5) :
    StepRowSem (pk, mu) (stepXmssR pk mu sig) (.xmssMerkleBlockB false false) (458 + 2 * l + 1) := by
  have hop := (stepXmssProgram_merkle l (by omega)).2
  rw [show (l + 1 == 6) = false from beq_eq_false_iff_ne.mpr (by omega)] at hop
  exact stepXmssR_sem pk mu sig _ _ (by omega) hop True.intro

theorem stepXmssR_merkleBin (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (l : Nat) (hl : l < 6) :
    (stepXmssR pk mu sig (458 + 2 * l + 1)).stIn =
      stepMerkleBIn (stepRegsAt (stepXmssR pk mu sig) (458 + 2 * l + 1)) := by
  have he := congrArg StepOpRow.stIn (stepXmssR_built pk mu sig (458 + 2 * l + 1) (by omega))
  rw [(stepXmssProgram_merkle l hl).2] at he
  exact he

set_option maxHeartbeats 800000 in
/-- Six constructed halvings end with zero cursor for every native XMSS leaf index. -/
theorem stepXmssR_merkle_cursor (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (leaf : Nat) (hleaf : leaf < 64)
    (hc : (stepRegsAt (stepXmssR pk mu sig) 458).cursor = Goldilocks.ofNat leaf) :
    (stepRegsAt (stepXmssR pk mu sig) 469).cursor = Goldilocks.zero := by
  let R := stepXmssR pk mu sig
  have hleafP : leaf < goldilocksPrime := Nat.lt_trans hleaf (by decide)
  have ha : ∀ l < 6, (stepRegsAt R (458 + 2 * l + 1)).cursor =
      Goldilocks.ofNat ((stepRegsAt R (458 + 2 * l)).cursor.val / 2) := by
    intro l hl
    rw [(stepSem_xmssMerkleBlockA (stepXmssR_merkleA pk mu sig l hl)).2.2.2]
    change stepAux R (458 + 2 * l) 1 = _
    rw [stepXmssR_aux pk mu sig _ 1 (by omega) (by decide) _ (stepXmssProgram_merkle l hl).1]
    rfl
  have hbefore : ∀ l, l < 6 → (stepRegsAt R (458 + 2 * l)).cursor = Goldilocks.ofNat (leaf / 2 ^ l) := by
    intro l
    induction l with
    | zero => intro _; simpa only [Nat.pow_zero, Nat.div_one] using hc
    | succ l ih =>
      intro hl
      have hb : stepRegsAt R (458 + 2 * l + 2) = _ :=
        (stepSem_xmssMerkleBlockB_inner (stepXmssR_merkleB pk mu sig l (by omega))).2
      rw [show 458 + 2 * (l + 1) = 458 + 2 * l + 2 by omega, hb]
      change (stepRegsAt R (458 + 2 * l + 1)).cursor = _
      rw [ha l (by omega), ih (by omega), Goldilocks.ofNat_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self leaf _) hleafP),
        Nat.div_div_eq_div_mul, Nat.pow_succ]
  have he := ha 5 (by decide)
  rw [hbefore 5 (by decide), Goldilocks.ofNat_val,
    Nat.mod_eq_of_lt (show leaf / 2 ^ 5 < goldilocksPrime by have := Nat.div_le_self leaf (2 ^ 5); omega)] at he
  have hz : leaf / 2 ^ 5 / 2 = 0 := by omega
  rw [hz] at he
  exact he


attribute [local irreducible] stepXmssR

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- Native acceptance establishes the entire non-padding XMSS execution. -/
theorem stepXmssNative_body (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) :
    StepRunAt (pk, computeMessageMu pk msg) (stepXmssR pk (computeMessageMu pk msg) sig)
      (signerProgramBody .xmssPoseidon2) 0 := by
  let mu := computeMessageMu pk msg
  let R := stepXmssR pk mu sig
  obtain ⟨ls, hlayers, hleaf, hV⟩ := stepXmssNative_layer pk msg sig h
  obtain ⟨hchk, hsum, hchains, hpath⟩ := stepXmssNative_digits pk _ ls _ hV
  obtain ⟨hhmsg, hrem0, hacc0, haddr0⟩ := stepXmssR_hmsg pk mu sig ls hlayers hleaf
  rw [← hhmsg] at hchk hsum
  have hdec := stepXmssR_decomp pk mu sig hchk hsum hacc0
  obtain ⟨_, hpack, _, _, hroot8, hkp8, hlo8, hhi8⟩ := stepDecomp_sem hdec hrem0 hacc0
  have hbound := stepForward_pack_bounds _ _ hpack
  have hwots := stepXmssR_wots pk mu sig hbound
  have haddr8 : StepAddrOk (stepRegsAt R 8) sig.statefulLeafIdx 0 :=
    ⟨hkp8.trans haddr0.kp, hlo8.trans haddr0.lo, hhi8.trans haddr0.hi⟩
  have hws := stepWots_sem hwots haddr8 (by decide) (by omega)
  have hcur := stepXmssR_merkle_cursor pk mu sig sig.statefulLeafIdx hleaf hws.2.2.2.2.2
  have hA := stepXmssR_merkleA pk mu sig
  have hBin := stepXmssR_merkleBin pk mu sig
  have hBnext : ∀ l, l + 1 < 6 → stepRegsAt R (458 + 2 * l + 2) =
      { stepRegsAt R (458 + 2 * l + 1) with work := (stepPermAt R (458 + 2 * l + 1)).b0 } := by
    intro l hl
    exact (stepSem_xmssMerkleBlockB_inner (stepXmssR_merkleB pk mu sig l (by omega))).2
  have hLayer := stepLayer_verify_forward (geom := xmssPoseidon2Geom) (ctr := ls.tswCtr)
    (layer := 0) (h := 6) (tD := 3) (kpN := sig.statefulLeafIdx) (tree := 0)
    hdec hwots hrem0 hacc0 haddr0 hA hBin hBnext hcur
    (by decide) (by omega) (by decide) (by decide)
    (by simp only [xmssPoseidon2Geom.public_eqs])
    (by simp only [xmssPoseidon2Geom.public_eqs])
    (by simp only [xmssPoseidon2Geom.public_eqs])
  have hLayerV := hLayer.2.1
  rw [hhmsg, stepXmssR_chain_values pk mu sig ls hlayers hchains,
    stepXmssR_path_values pk mu sig ls hlayers hpath] at hLayerV
  have hV' : verifyWotsLayer xmssPoseidon2Geom pk 0 0 sig.statefulLeafIdx
      (computeHmsgStateful pk sig.rRand mu sig.statefulLeafIdx ls.tswCtr) ls =
        some (stepPermAt R 469).b0 := hLayerV
  have hroot : (stepPermAt R 469).b0 = pk.pkRoot := Option.some.inj (hV'.symm.trans hV)
  have hst : (R 469).stIn = stepXmssInput pk mu (.xmssMerkleBlockB true true)
      (R 469).prevState (stepXmssAux sig (.xmssMerkleBlockB true true) (R 469).prevState) := by
    have he := congrArg StepOpRow.stIn (stepXmssR_built pk mu sig 469 (by decide))
    have hop : (buildSignerProgram .xmssPoseidon2).getD 469 .idle = .xmssMerkleBlockB true true := stepXmssProgram_at_469
    rw [hop] at he
    exact he
  have hroot' : (poseidon2Perm12 (stepXmssInput pk mu (.xmssMerkleBlockB true true)
      (R 469).prevState (stepXmssAux sig (.xmssMerkleBlockB true true) (R 469).prevState))).b0 = pk.pkRoot := by
    rw [← hst]
    exact hroot
  have htop : StepRowSem (pk, mu) R (.xmssMerkleBlockB true true) 469 := by
    apply stepXmssR_sem pk mu sig 469 (.xmssMerkleBlockB true true) (by decide) stepXmssProgram_at_469
    refine ⟨hcur, ?_⟩
    intro i hi
    rcases i with _ | _ | _ | _ | i
    · simpa only [Poseidon2State12.toList_eq, Lane4.toList_eq,
        List.getD_cons_zero, List.getD_cons_succ] using congrArg Lane4.x0 hroot'
    · simpa only [Poseidon2State12.toList_eq, Lane4.toList_eq,
        List.getD_cons_zero, List.getD_cons_succ] using congrArg Lane4.x1 hroot'
    · simpa only [Poseidon2State12.toList_eq, Lane4.toList_eq,
        List.getD_cons_zero, List.getD_cons_succ] using congrArg Lane4.x2 hroot'
    · simpa only [Poseidon2State12.toList_eq, Lane4.toList_eq,
        List.getD_cons_zero, List.getD_cons_succ] using congrArg Lane4.x3 hroot'
    · exact False.elim (by omega)
  have hmerkle : StepRunAt (pk, mu) R (stepMerkleOps 0 6 true) 458 := by
    intro i hi
    change i < 12 at hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    · exact hA 0 (by decide)
    · exact stepXmssR_merkleB pk mu sig 0 (by decide)
    · exact hA 1 (by decide)
    · exact stepXmssR_merkleB pk mu sig 1 (by decide)
    · exact hA 2 (by decide)
    · exact stepXmssR_merkleB pk mu sig 2 (by decide)
    · exact hA 3 (by decide)
    · exact stepXmssR_merkleB pk mu sig 3 (by decide)
    · exact hA 4 (by decide)
    · exact stepXmssR_merkleB pk mu sig 4 (by decide)
    · exact hA 5 (by decide)
    · exact htop
    · exact False.elim (by omega)
  have hpush : StepRunAt (pk, mu) R (pushLayerWotsAndMerkle 0 6 true) 8 := by
    rw [pushLayerWotsAndMerkle_eq]
    apply stepForwardRunAt_append
    · exact hwots
    · rw [stepWotsOps_length]
      exact hmerkle
  simp only [signerProgramBody.public_eqs]
  apply stepForwardRunAt_append
  · apply stepForwardRunAt_append
    · intro i hi
      change i < 3 at hi
      rcases i with _ | _ | _ | i
      · exact stepXmssR_sem pk mu sig 0 _ (by decide) stepXmssProgram_at_0 True.intro
      · exact stepXmssR_sem pk mu sig 1 _ (by decide) stepXmssProgram_at_1 True.intro
      · exact stepXmssR_sem pk mu sig 2 _ (by decide) stepXmssProgram_at_2 True.intro
      · exact False.elim (by omega)
    · exact hdec
  · exact hpush



/-- Native XMSS acceptance constructs an accepted 512-row active signer table. -/
theorem stepXmssRows_of_verify (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) :
    stepOp256TableOk .xmssPoseidon2 [some (pk, computeMessageMu pk msg)]
      (stepXmssRows pk (computeMessageMu pk msg) sig) = true := by
  apply (stepXmssRows_table_iff pk (computeMessageMu pk msg) sig).mpr
  intro i row hr
  have hi : i < 512 := by
    have hh := (List.getElem?_eq_some_iff.mp hr).1
    rwa [stepXmssRows_length] at hh
  have he : row = stepXmssR pk (computeMessageMu pk msg) sig i :=
    Option.some.inj (hr.symm.trans (stepXmssR_at pk _ sig i hi))
  subst row
  by_cases hib : i < 470
  · have hbody := stepXmssNative_body pk msg sig h
    have hiBody : i < (signerProgramBody .xmssPoseidon2).length := by
      rw [buildSignerProgram_length.1]; exact hib
    have hs := hbody i hiBody
    have hop : (buildSignerProgram .xmssPoseidon2).getD i .idle =
        (signerProgramBody .xmssPoseidon2)[i] := by
      simp only [buildSignerProgram.public_eqs]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hiBody,
        List.getElem?_eq_getElem hiBody, Option.getD_some]
    rw [hop]
    simpa only [Nat.zero_add] using hs.2.1
  · rw [stepXmssProgram_idle i hi (by omega)]
    simp only [stepOpKindAndC0.public_eqs, stepOpGuardResiduals, allZeroGoldilocks_eq, List.all_nil]


/-- An active committee entry carries its message and signature; `none` is inactive. -/
abbrev StepXmssEntry := Option (AggValidatorPk × List UInt8 × AggNativeSignature)

def stepXmssEntrySlot : StepXmssEntry → StepOpSlot
  | none => none
  | some (pk, msg, _) => some (pk, computeMessageMu pk msg)

def stepXmssEntryRows : StepXmssEntry → List StepOpRow
  | none => stepInactiveRows .xmssPoseidon2
  | some (pk, msg, sig) => stepXmssRows pk (computeMessageMu pk msg) sig

def StepXmssEntryValid : StepXmssEntry → Prop
  | none => True
  | some (pk, msg, sig) => verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true

def stepXmssCommitteeSlots (entries : List StepXmssEntry) : List StepOpSlot :=
  entries.map stepXmssEntrySlot

def stepXmssCommitteeRows (entries : List StepXmssEntry) : List StepOpRow :=
  entries.flatMap stepXmssEntryRows

theorem stepXmssEntry_length (entry : StepXmssEntry) : (stepXmssEntryRows entry).length = 512 := by
  cases entry with
  | none => simp only [stepXmssEntryRows, stepInactiveRows, List.length_replicate, stepOpRowsPerSigner.public_eqs]
  | some p => exact stepXmssRows_length ..

theorem stepXmssEntry_table (entry : StepXmssEntry) (h : StepXmssEntryValid entry) :
    stepOp256TableOk .xmssPoseidon2 [stepXmssEntrySlot entry] (stepXmssEntryRows entry) = true := by
  cases entry with
  | none => simpa only [stepXmssEntryRows, stepXmssEntrySlot, stepInactiveRows,
      stepOpRowsPerSigner.public_eqs, Nat.one_mul, List.replicate_one] using
      stepInactiveCommittee_table .xmssPoseidon2 1 (by decide)
  | some p => exact stepXmssRows_of_verify p.1 p.2.1 p.2.2 h

theorem stepXmssCommittee_length (entries : List StepXmssEntry) :
    (stepXmssCommitteeRows entries).length = entries.length * 512 := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    change (stepXmssEntryRows e ++ stepXmssCommitteeRows es).length = (es.length + 1) * 512
    rw [List.length_append, stepXmssEntry_length, ih, Nat.add_mul]
    omega

/-- Indexing a concatenation of fixed-width signer blocks. -/
theorem stepXmssCommittee_get (entries : List StepXmssEntry) (i : Nat)
    (hi : i / 512 < entries.length) :
    (stepXmssCommitteeRows entries)[i]? =
      (stepXmssEntryRows (entries.getD (i / 512) none))[i % 512]? := by
  induction entries generalizing i with
  | nil => simp at hi
  | cons e es ih =>
    change (stepXmssEntryRows e ++ stepXmssCommitteeRows es)[i]? = _
    by_cases hlt : i < 512
    · rw [List.getElem?_append_left (by rw [stepXmssEntry_length]; exact hlt),
        Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, List.getD_cons_zero]
    · rw [List.getElem?_append_right (by rw [stepXmssEntry_length]; omega), stepXmssEntry_length]
      have hk : (i - 512) / 512 < es.length := by simp only [List.length_cons] at hi; omega
      rw [ih (i - 512) hk]
      have hd : i / 512 = (i - 512) / 512 + 1 := by omega
      have hm : i % 512 = (i - 512) % 512 := by omega
      rw [hd, hm, List.getD_cons_succ]

theorem stepXmssEntry_boundary (entry : StepXmssEntry) (hv : StepXmssEntryValid entry)
    (j : Nat) (row : StepOpRow) (hr : (stepXmssEntryRows entry)[j]? = some row) :
    (∀ s < 44, j % 512 = 0 → row.prevState.getD s Goldilocks.zero = Goldilocks.zero) ∧
    (∀ s < 44, j % 512 + 1 = 512 → row.nextState.getD s Goldilocks.zero = Goldilocks.zero) := by
  have hz := stepOp256TableOk_row_at .xmssPoseidon2 [stepXmssEntrySlot entry] _ j row
    (stepXmssEntry_table entry hv) hr
  simp only [stepOp256RowResiduals_def, allZeroGoldilocks_append, Bool.and_eq_true, stepOpRowsPerSigner.public_eqs] at hz
  exact (stepOpBoundaryResiduals_iff 512 (j % 512) row).mp hz.1.2

/-- Native acceptance of each active entry constructs a table with arbitrary inactive slots. -/
theorem stepXmssCommittee_of_verify (entries : List StepXmssEntry)
    (hne : 0 < entries.length) (hv : ∀ entry ∈ entries, StepXmssEntryValid entry) :
    stepOp256TableOk .xmssPoseidon2 (stepXmssCommitteeSlots entries)
      (stepXmssCommitteeRows entries) = true := by
  have hlen := stepXmssCommittee_length entries
  have hm : ∀ k, k < entries.length → entries.getD k none ∈ entries := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  have hloc : ∀ k, k < entries.length →
      stepOp256TableOk .xmssPoseidon2 [stepXmssEntrySlot (entries.getD k none)]
        (stepXmssEntryRows (entries.getD k none)) = true :=
    fun k hk => stepXmssEntry_table _ (hv _ (hm k hk))
  have hidx : ∀ i row, (stepXmssCommitteeRows entries)[i]? = some row → i / 512 < entries.length := by
    intro i row hr
    have hi := (List.getElem?_eq_some_iff.mp hr).1
    rw [hlen] at hi
    omega
  apply (stepOp256TableOk_iff_rows _ _ _).mpr
  refine ⟨by simpa only [stepXmssCommitteeSlots, List.length_map] using hne,
    by simpa only [stepXmssCommitteeSlots, List.length_map, stepOpRowsPerSigner.public_eqs] using hlen, ?_, ?_, ?_⟩
  · intro row hr
    obtain ⟨entry, he, hr⟩ := List.mem_flatMap.mp hr
    exact ((stepOp256TableOk_iff_rows _ _ _).mp (stepXmssEntry_table entry (hv entry he))).2.2.1 row hr
  · intro i row hr
    have hk := hidx i row hr
    have hrow := hr
    rw [stepXmssCommittee_get entries i hk] at hrow
    have hz := stepOp256TableOk_row_at .xmssPoseidon2 _ _ (i % 512) row (hloc (i / 512) hk) hrow
    have hj : i % 512 < 512 := Nat.mod_lt _ (by decide)
    simp only [stepOpRowsPerSigner.public_eqs, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, List.getD_cons_zero] at hz
    have hs : (stepXmssCommitteeSlots entries).getD (i / 512) none =
        stepXmssEntrySlot (entries.getD (i / 512) none) := by
      simp only [stepXmssCommitteeSlots, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
    simp only [stepOpRowsPerSigner.public_eqs]
    change allZeroGoldilocks (stepOp256RowResiduals .xmssPoseidon2
      ((stepXmssCommitteeSlots entries).getD (i / 512) none) (i % 512) row) = true
    rw [hs]
    exact hz
  · intro i r r' hr hr' s hs
    have hk := hidx i r hr
    have hk' := hidx (i + 1) r' hr'
    rw [stepXmssCommittee_get entries i hk] at hr
    rw [stepXmssCommittee_get entries (i + 1) hk'] at hr'
    by_cases hlast : i % 512 = 511
    · have hz := stepXmssEntry_boundary _ (hv _ (hm (i / 512) hk)) (i % 512) r hr
      have hz' := stepXmssEntry_boundary _ (hv _ (hm ((i + 1) / 512) hk')) ((i + 1) % 512) r' hr'
      rw [hz.2 s hs (by omega), hz'.1 s hs (by omega)]
    · have hd : (i + 1) / 512 = i / 512 := by omega
      have hj : (i + 1) % 512 = i % 512 + 1 := by omega
      rw [hd, hj] at hr'
      exact ((stepOp256TableOk_iff_rows _ _ _).mp (hloc (i / 512) hk)).2.2.2.2
        (i % 512) r r' hr hr' s hs


/-- Associate signatures and messages with the public slot indices. -/
def stepXmssSlotEntries (slots : List StepOpSlot) (msg : Nat → List UInt8)
    (sig : Nat → AggNativeSignature) : List StepXmssEntry :=
  (List.range slots.length).map fun i =>
    (slots.getD i none).map fun pub => (pub.1, msg i, sig i)

def stepXmssSlotsRows (slots : List StepOpSlot) (msg : Nat → List UInt8)
    (sig : Nat → AggNativeSignature) : List StepOpRow :=
  stepXmssCommitteeRows (stepXmssSlotEntries slots msg sig)

/-- Direct public-slot interface, permitting active and inactive slots in any order. -/
theorem stepXmssSlotsRows_of_verify (slots : List StepOpSlot) (msg : Nat → List UInt8)
    (sig : Nat → AggNativeSignature) (hne : 0 < slots.length)
    (h : ∀ i pub, slots[i]? = some (some pub) →
      pub.2 = computeMessageMu pub.1 (msg i) ∧
      verifyAggNativeSig xmssPoseidon2Geom pub.1 (msg i) (sig i) = true) :
    stepOp256TableOk .xmssPoseidon2 slots (stepXmssSlotsRows slots msg sig) = true := by
  have hs : stepXmssCommitteeSlots (stepXmssSlotEntries slots msg sig) = slots := by
    apply List.ext_getElem
    · simp only [stepXmssCommitteeSlots, stepXmssSlotEntries, List.length_map, List.length_range]
    · intro i hi hi'
      simp only [stepXmssCommitteeSlots, stepXmssSlotEntries, List.getElem_map, List.getElem_range]
      have hd : slots.getD i none = slots[i] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      rw [hd]
      cases he : slots[i] with
      | none => rfl
      | some pub =>
        have hh := h i pub (by rw [List.getElem?_eq_getElem hi', he])
        change some (pub.1, computeMessageMu pub.1 (msg i)) = some pub
        rw [← hh.1]
  have hv : ∀ entry ∈ stepXmssSlotEntries slots msg sig, StepXmssEntryValid entry := by
    intro entry he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    have hi' : i < slots.length := List.mem_range.mp hi
    have hd : slots.getD i none = slots[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rw [hd]
    cases he : slots[i] with
    | none => exact True.intro
    | some pub => exact (h i pub (by rw [List.getElem?_eq_getElem hi', he])).2
  have ht := stepXmssCommittee_of_verify (stepXmssSlotEntries slots msg sig)
    (by simpa only [stepXmssSlotEntries, List.length_map, List.length_range] using hne) hv
  rw [hs] at ht
  exact ht

theorem stepXmssNative_profile (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) : pk.profile = .xmssPoseidon2 := by
  simp only [verifyAggNativeSig.public_eqs] at h
  split at h
  · contradiction
  · rename_i hc
    have hf := Bool.eq_false_iff.mpr hc
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hf
    simpa only [xmssPoseidon2Geom.public_eqs] using hf.1.1.2

/-- An accepted signature survives the complete native-to-table-to-native round trip. -/
theorem stepXmssRows_roundTrip (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) :
    verifyAggNativeSig xmssPoseidon2Geom pk msg
      (stepXmssSig (stepOpSlotRow .xmssPoseidon2 (stepXmssRows pk (computeMessageMu pk msg) sig) 0)) = true :=
  stepOp256TableOk_xmss_extract _ _ 0 (pk, computeMessageMu pk msg) msg
    (stepXmssRows_of_verify pk msg sig h) rfl (stepXmssNative_profile pk msg sig h) rfl

set_option maxRecDepth 4096 in
/-- The remaining execution checks are consequences of the original guard equations. -/
theorem stepXmss_checks_of_seed_guards (pk : AggValidatorPk) (mu : Digest5)
    (sig : AggNativeSignature) (op : StepOp) (prev : List Goldilocks)
    (hg : allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig op prev))) = true) :
    StepXmssChecks pk mu sig op prev := by
  cases op <;> try exact True.intro
  case hmsgDecompLimb l =>
    simp only [stepOpKindAndC0.public_eqs, stepOpGuardResiduals, allZeroGoldilocks_append,
      Bool.and_eq_true] at hg
    refine ⟨(stepLimb63Decomp_allZero_iff _ _).mp hg.1 |>.1, ?_⟩
    intro hl
    have hh := hg.2
    simp only [hl, ↓reduceIte, allZeroGoldilocks_eq, List.all_cons, List.all_nil,
      Bool.and_true, beq_iff_eq, g_sub_eq_zero_iff] at hh
    simpa only [hl] using hh
  case wotsTellPairAbsorb pair =>
    intro hp
    simp only [stepOpKindAndC0.public_eqs, stepOpGuardResiduals, hp, beq_self_eq_true,
      ↓reduceIte, allZeroGoldilocks_append, Bool.and_eq_true] at hg
    exact (allZero_map_iff _ _).mp hg.1
  case xmssMerkleBlockB a b =>
    cases a <;> cases b <;> try exact True.intro
    simp only [stepOpKindAndC0.public_eqs, stepOpGuardResiduals, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, allZeroGoldilocks_append, Bool.and_eq_true] at hg
    constructor
    · have hh := hg.2.1
      simp only [allZeroGoldilocks_eq, List.all_cons, List.all_nil, Bool.and_true,
        beq_iff_eq] at hh
      exact hh
    · intro i hi
      have hh := g_sub_eq_zero_iff.mp ((allZero_map_iff _ _).mp hg.2.2 i hi)
      have hp := stepOp256_groupA_exact
        (stepXmssSeedRow pk mu sig (.xmssMerkleBlockB true true) prev)
        (stepOpHonestPermutationRow_groupA ..)
      change (stepOpPermTrace _).1.toList.getD i Goldilocks.zero = _ at hh
      rw [hp] at hh
      exact hh

/-- Native acceptance discharges every arithmetic and terminal execution check. -/
theorem stepXmssChecks_of_verify (pk : AggValidatorPk) (msg : List UInt8)
    (sig : AggNativeSignature) (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true)
    (i : Nat) (row : StepOpRow)
    (hr : (stepXmssRows pk (computeMessageMu pk msg) sig)[i]? = some row) :
    StepXmssChecks pk (computeMessageMu pk msg) sig
      ((buildSignerProgram .xmssPoseidon2).getD i .idle) row.prevState := by
  let mu := computeMessageMu pk msg
  have hg := (stepXmssRows_table_iff pk mu sig).mp (stepXmssRows_of_verify pk msg sig h) i row hr
  obtain ⟨op, state, hop, he⟩ := stepForwardRun_at (pk, mu) (stepXmssCells pk mu sig)
    (buildSignerProgram .xmssPoseidon2) stepForwardZero i row hr
  have hopD : (buildSignerProgram .xmssPoseidon2).getD i .idle = op := by
    rw [List.getD_eq_getElem?_getD, hop]; rfl
  rw [hopD, he] at hg ⊢
  change allZeroGoldilocks (stepOpGuardResiduals _ _
    (stepOpRowInputs (pk, mu) (populateStepOpNext _ _ _ (stepXmssSeedRow pk mu sig op state)))) = true at hg
  rw [populateStepOpNext_inputs, stepOpGuardResiduals_congr_next] at hg
  exact stepXmss_checks_of_seed_guards pk mu sig op state hg

end StepOpForward
end Qsag
end

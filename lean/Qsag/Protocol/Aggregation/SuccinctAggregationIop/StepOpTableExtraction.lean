module


public import Qsag.Protocol.Aggregation.SuccinctAggregationIop.RowArithmetizationSoundness

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv
set_option autoImplicit false
set_option exponentiation.threshold 2048
attribute [local irreducible] verifyUpperLayers
attribute [local irreducible] computeMessageMu
attribute [local irreducible] verifyAggNativeSigStateful verifyAggNativeSigStateless

/-! ### The 256-column `StepOp` execution table and its inter-row shift constraints (`trace.rs`) -/

section StepOpTable

local infixl:65 " +ₚ " => Goldilocks.add
local infixl:65 " -ₚ " => Goldilocks.sub
local infixl:70 " *ₚ " => Goldilocks.mul
local notation "‹" n "›" => Goldilocks.ofNat n

/-- `NUM_TRACE_COLS`. -/
def stepOpNumCols : Nat := 256

/-- `NUM_STATE_LIMBS`: the carried state registers `st[0..44]`. -/
def stepOpNumStateLimbs : Nat := 44

/-- `ST_CUR_ROOT` (4 limbs). -/
abbrev stCurRoot : Nat := 0
/-- `ST_KP_IDX`. -/
abbrev stKpIdx : Nat := 4
/-- `ST_TREE_LO`. -/
abbrev stTreeLo : Nat := 5
/-- `ST_TREE_HI`. -/
abbrev stTreeHi : Nat := 6
/-- `ST_REM_PACK` (6 limbs). -/
abbrev stRemPack : Nat := 7
/-- `ST_MAIN_SPONGE` (12 limbs). -/
abbrev stMainSponge : Nat := 13
/-- `ST_SUB_SPONGE` (12 limbs). -/
abbrev stSubSponge : Nat := 25
/-- `ST_WORK` (4 limbs). -/
abbrev stWork : Nat := 37
/-- `ST_CURSOR_IDX`. -/
abbrev stCursorIdx : Nat := 41
/-- `ST_ACC_OR_U1`. -/
abbrev stAccOrU1 : Nat := 42
/-- `ST_WOTS_U2`. -/
abbrev stWotsU2 : Nat := 43

/-- One row of the execution table, grouped by the column blocks of `trace.rs`:
    `COL_ST_IN = 0..12`, `COL_SBOX_OUT = 12..130` (4 external rounds of 12 lanes, 22 internal
    rounds, 4 external rounds of 12 lanes), `COL_PREV_STATE = 130..174`,
    `COL_NEXT_STATE = 174..218`, `COL_AUX = 218..256`. -/
structure StepOpRow where
  stIn        : Poseidon2State12
  initExtSbox : List Poseidon2State12
  intSbox     : List Goldilocks
  termExtSbox : List Poseidon2State12
  prevState   : List Goldilocks
  nextState   : List Goldilocks
  aux         : List Goldilocks
  deriving DecidableEq, Repr

/-- The column blocks have their `trace.rs` widths. -/
def StepOpRow.wellShaped (r : StepOpRow) : Bool :=
  r.initExtSbox.length == 4 && r.intSbox.length == 22 && r.termExtSbox.length == 4 &&
  r.prevState.length == 44 && r.nextState.length == 44 && r.aux.length == 38

/-- The cells of a row in `trace.rs` column order. -/
def StepOpRow.cells (r : StepOpRow) : List Goldilocks :=
  r.stIn.toList ++ r.initExtSbox.flatMap Poseidon2State12.toList ++ r.intSbox ++
    r.termExtSbox.flatMap Poseidon2State12.toList ++ r.prevState ++ r.nextState ++ r.aux

private theorem flatMap_state12_length :
    ∀ (l : List Poseidon2State12), (l.flatMap Poseidon2State12.toList).length = 12 * l.length
  | [] => rfl
  | s :: l => by
    have h12 : s.toList.length = 12 := Poseidon2State12.toList_length s
    rw [List.flatMap_cons, List.length_append, flatMap_state12_length l, List.length_cons, h12]
    omega

/-- A well-shaped row has exactly `NUM_TRACE_COLS = 256` cells. -/
theorem StepOpRow.cells_length (r : StepOpRow) (h : r.wellShaped = true) :
    r.cells.length = stepOpNumCols := by
  unfold StepOpRow.wellShaped at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have h12 : r.stIn.toList.length = 12 := Poseidon2State12.toList_length r.stIn
  have hc : r.cells.length =
      r.stIn.toList.length + 12 * r.initExtSbox.length + r.intSbox.length +
        12 * r.termExtSbox.length + r.prevState.length + r.nextState.length + r.aux.length := by
    unfold StepOpRow.cells
    simp only [List.length_append, flatMap_state12_length]
  unfold stepOpNumCols
  omega

/-- Deterministic step opcodes of the per-signer state machine (`StepOp` in `trace.rs`). -/
inductive StepOp where
  | idle
  | statefulHmsgBlock0
  | statefulHmsgBlock1
  | statefulHmsgSqueeze
  | statelessDeriveBlock0
  | statelessDeriveBlock1
  | statelessDecompLimb (limbIdx : Nat)
  | forsRootsSpongeInit
  | forsLeafHash (treeJ packSlot : Nat)
  | forsMerkleBlockA (treeJ lvl : Nat)
  | forsMerkleBlockB (lvl : Nat) (isTreeLast isOddTree : Bool)
  | forsRootsPairAbsorb (pairIdx : Nat)
  | forsRootsFinalSqueeze
  | detTreeHmsgBlock0 (layer : Nat)
  | detTreeHmsgBlock1 (layer : Nat)
  | hmsgDecompLimb (limbIdx : Nat)
  | wotsTellInit (layer : Nat)
  | wotsChainStep0 (layer chain packSlot : Nat)
  | wotsChainStep1 (layer chain : Nat)
  | wotsChainStep2 (layer chain : Nat) (isOdd : Bool)
  | wotsTellPairAbsorb (pairIdx : Nat)
  | wotsTellFinalSqueeze
  | xmssMerkleBlockA (layer lvl : Nat)
  | xmssMerkleBlockB (isLayerLast isTopFinal : Bool)
  deriving DecidableEq, Repr

/-- Algebraic constraint class of a step (`ConstraintKind` in `trace.rs`): the per-step public
    constants `layer`, `chain`, `tree_j`, `lvl` are factored into the scalar `step_c0`. -/
inductive StepConstraintKind where
  | idle
  | statefulHmsgBlock0
  | statefulHmsgBlock1
  | statefulHmsgSqueeze
  | statelessDeriveBlock0
  | statelessDeriveBlock1
  | statelessDecompLimb (limbIdx : Nat)
  | forsRootsSpongeInit
  | forsLeafHash (packSlot : Nat)
  | forsMerkleBlockA
  | forsMerkleBlockB (isTreeLast isOddTree : Bool)
  | forsRootsPairAbsorb (isLastPair : Bool)
  | forsRootsFinalSqueeze
  | detTreeHmsgBlock0
  | detTreeHmsgBlock1
  | hmsgDecompLimb (limbIdx : Nat)
  | wotsTellInit
  | wotsChainStep0 (packSlot : Nat)
  | wotsChainStep1
  | wotsChainStep2 (isOdd : Bool)
  | wotsTellPairAbsorb (isLastPair : Bool)
  | wotsTellFinalSqueeze
  | xmssMerkleBlockA
  | xmssMerkleBlockB (isLayerLast isTopFinal : Bool)
  deriving DecidableEq, Repr

/-- `wots_pack_slot`: the `ST_REM_PACK` limb holding the remaining-step count of a chain. -/
def wotsPackSlot (chain : Nat) : Nat :=
  if chain < 26 then 0 else if chain < 52 then 1 else if chain < 78 then 2
  else if chain < 103 then 3 else 4

/-- First chain of a `wots_pack_slot`. -/
def wotsPackSlotStart : Nat → Nat
  | 0 => 0
  | 1 => 26
  | 2 => 52
  | 3 => 78
  | _ => 103

/-- `push_layer_wots_and_merkle`: one WOTS+C layer (`T_ell` sponge interleaved with the 128
    three-step chains) followed by its subtree Merkle path. -/
def pushLayerWotsAndMerkle (layer subHeight : Nat) (isTopFinal : Bool) : List StepOp :=
  [StepOp.wotsTellInit layer] ++
  (List.range 64).flatMap (fun pair =>
    (List.range 2).flatMap (fun sub =>
      [StepOp.wotsChainStep0 layer (2 * pair + sub) (wotsPackSlot (2 * pair + sub)),
       StepOp.wotsChainStep1 layer (2 * pair + sub),
       StepOp.wotsChainStep2 layer (2 * pair + sub) (sub == 1)]) ++
    [StepOp.wotsTellPairAbsorb pair]) ++
  [StepOp.wotsTellFinalSqueeze] ++
  (List.range subHeight).flatMap (fun lvl =>
    [StepOp.xmssMerkleBlockA layer lvl,
     StepOp.xmssMerkleBlockB (lvl + 1 == subHeight) ((lvl + 1 == subHeight) && isTopFinal)])

/-- `rows_per_signer`. -/
def stepOpRowsPerSigner : AggSigProfile → Nat
  | .xmssPoseidon2 => 512
  | .corduroyPoseidon2 => 8192

/-- The opcodes of one signer before `Idle` padding. -/
def signerProgramBody : AggSigProfile → List StepOp
  | .xmssPoseidon2 =>
    [StepOp.statefulHmsgBlock0, StepOp.statefulHmsgBlock1, StepOp.statefulHmsgSqueeze] ++
    (List.range 5).map StepOp.hmsgDecompLimb ++
    pushLayerWotsAndMerkle 0 6 true
  | .corduroyPoseidon2 =>
    [StepOp.statelessDeriveBlock0, StepOp.statelessDeriveBlock1] ++
    (List.range 7).map StepOp.statelessDecompLimb ++
    [StepOp.forsRootsSpongeInit] ++
    (List.range 16).flatMap (fun pair =>
      (List.range 2).flatMap (fun sub =>
        [StepOp.forsLeafHash (2 * pair + sub) ((2 * pair + sub) / 6)] ++
        (List.range 8).flatMap (fun lvl =>
          [StepOp.forsMerkleBlockA (2 * pair + sub) lvl,
           StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) (sub == 1)])) ++
      [StepOp.forsRootsPairAbsorb pair]) ++
    [StepOp.forsRootsFinalSqueeze] ++
    (List.range 16).flatMap (fun layer =>
      [StepOp.detTreeHmsgBlock0 layer, StepOp.detTreeHmsgBlock1 layer] ++
      (List.range 5).map StepOp.hmsgDecompLimb ++
      pushLayerWotsAndMerkle layer 4 (layer + 1 == 16))

/-- `build_signer_program`: the fixed-length program shared by prover and verifier. -/
def buildSignerProgram (profile : AggSigProfile) : List StepOp :=
  signerProgramBody profile ++
    List.replicate (stepOpRowsPerSigner profile - (signerProgramBody profile).length) StepOp.idle

/-- The program fills exactly `rows_per_signer` rows and ends in at least one `Idle` row
    (`470 < 512` and `8011 < 8192`). -/
theorem buildSignerProgram_length :
    (signerProgramBody .xmssPoseidon2).length = 470 ∧
    (signerProgramBody .corduroyPoseidon2).length = 8011 ∧
    (buildSignerProgram .xmssPoseidon2).length = 512 ∧
    (buildSignerProgram .corduroyPoseidon2).length = 8192 := by
  decide +kernel

/-- `step_op_to_kind_and_c0`: constraint class and per-step public constant `step_c0`. -/
def stepOpKindAndC0 : StepOp → StepConstraintKind × Nat
  | .idle => (.idle, 0)
  | .statefulHmsgBlock0 => (.statefulHmsgBlock0, 0)
  | .statefulHmsgBlock1 => (.statefulHmsgBlock1, 0)
  | .statefulHmsgSqueeze => (.statefulHmsgSqueeze, 0)
  | .statelessDeriveBlock0 => (.statelessDeriveBlock0, 0)
  | .statelessDeriveBlock1 => (.statelessDeriveBlock1, 0)
  | .statelessDecompLimb l => (.statelessDecompLimb l, 0)
  | .forsRootsSpongeInit => (.forsRootsSpongeInit, 0)
  | .forsLeafHash j slot => (.forsLeafHash slot, j * 2 ^ 8)
  | .forsMerkleBlockA j lvl => (.forsMerkleBlockA, (lvl + 1) * 2 ^ 32 + j * 2 ^ (7 - lvl))
  | .forsMerkleBlockB _ isTreeLast isOddTree => (.forsMerkleBlockB isTreeLast isOddTree, 0)
  | .forsRootsPairAbsorb pair => (.forsRootsPairAbsorb (pair + 1 == 16), 0)
  | .forsRootsFinalSqueeze => (.forsRootsFinalSqueeze, 0)
  | .detTreeHmsgBlock0 layer => (.detTreeHmsgBlock0, layer * 2 ^ 32)
  | .detTreeHmsgBlock1 _ => (.detTreeHmsgBlock1, 0)
  | .hmsgDecompLimb l => (.hmsgDecompLimb l, 0)
  | .wotsTellInit layer => (.wotsTellInit, layer * 2 ^ 32)
  | .wotsChainStep0 layer chain slot => (.wotsChainStep0 slot, layer * 2 ^ 44 + chain * 2 ^ 4)
  | .wotsChainStep1 layer chain => (.wotsChainStep1, layer * 2 ^ 44 + chain * 2 ^ 4 + 1)
  | .wotsChainStep2 layer chain isOdd =>
    (.wotsChainStep2 isOdd, layer * 2 ^ 44 + chain * 2 ^ 4 + 2)
  | .wotsTellPairAbsorb pair => (.wotsTellPairAbsorb (pair + 1 == 64), 0)
  | .wotsTellFinalSqueeze => (.wotsTellFinalSqueeze, 0)
  | .xmssMerkleBlockA layer lvl => (.xmssMerkleBlockA, layer * 2 ^ 48 + (lvl + 1) * 2 ^ 32)
  | .xmssMerkleBlockB isLayerLast isTopFinal => (.xmssMerkleBlockB isLayerLast isTopFinal, 0)

/-- Row values one opcode's transition constraints read (`OpRowInputs` in `trace.rs`). -/
structure StepOpRowInputs where
  prev    : Nat → Goldilocks
  next    : Nat → Goldilocks
  aux     : Nat → Goldilocks
  stIn    : Nat → Goldilocks
  permOut : Nat → Goldilocks
  pkSeed  : Nat → Goldilocks
  pkRoot  : Nat → Goldilocks
  mu      : Nat → Goldilocks

/-- `bool_check_generic`: `b * (1 - b)`. -/
def stepBoolCheck (b : Goldilocks) : Goldilocks := b *ₚ (Goldilocks.one -ₚ b)

/-- `Σ_{i < n} f i * w i`, accumulated from zero in index order. -/
def stepWeightedSum (f : Nat → Goldilocks) (w : Nat → Nat) (n : Nat) : Goldilocks :=
  (List.range n).foldl (fun acc i => acc +ₚ (f i *ₚ ‹w i›)) Goldilocks.zero

/-- `Σ_{i < n} f i`, accumulated from zero in index order. -/
def stepPlainSum (f : Nat → Goldilocks) (n : Nat) : Goldilocks :=
  (List.range n).foldl (fun acc i => acc +ₚ f i) Goldilocks.zero

/-- `j` lies in the register block `[a, a + n)`. -/
@[expose] def stepInBlock (a n j : Nat) : Bool := decide (a ≤ j) && decide (j < a + n)

/-- `check_carry_unchanged`: every state limb outside `changed` is carried, `next = prev`. -/
def stepCarryUnchanged (x : StepOpRowInputs) (changed : Nat → Bool) : List Goldilocks :=
  (List.range 44).filterMap fun j => if changed j then none else some (x.next j -ₚ x.prev j)

/-- `check_zero_elsewhere`: every state limb outside `kept` is zero in `next`. -/
def stepZeroElsewhere (x : StepOpRowInputs) (kept : Nat → Bool) : List Goldilocks :=
  (List.range 44).filterMap fun j => if kept j then none else some (x.next j)

/-- `next[base + i] = perm_out[i]` for `i < n`. -/
def stepNextIsPerm (x : StepOpRowInputs) (base n : Nat) : List Goldilocks :=
  (List.range n).map fun i => x.next (base + i) -ₚ x.permOut i

/-- Base-4 digits `aux[0..31]`, top bit `aux[31]`, and the reconstruction
    `prev[ST_MAIN_SPONGE + l] = Σ aux[i] 4^i + aux[31] 2^62` of a `< 2^63` limb. -/
def stepLimb63Decomp (x : StepOpRowInputs) (l : Nat) : List Goldilocks :=
  (List.range 31).map (fun i => quarticBase4 (x.aux i)) ++
  [stepBoolCheck (x.aux 31),
   x.prev (stMainSponge + l) -ₚ
     (stepWeightedSum x.aux (fun i => 4 ^ i) 31 +ₚ (x.aux 31 *ₚ ‹2 ^ 62›))]

/-- Byte `sub` assembled from four base-4 digits of the limb. -/
def stepByteVal (x : StepOpRowInputs) (sub : Nat) : Goldilocks :=
  ((x.aux (4 * sub) +ₚ (x.aux (4 * sub + 1) *ₚ ‹4›)) +ₚ (x.aux (4 * sub + 2) *ₚ ‹16›)) +ₚ
    (x.aux (4 * sub + 3) *ₚ ‹64›)

/-- `expected_next[j]` after packing FORS indices `firstJ .. firstJ + count` (six bytes per
    `ST_REM_PACK` limb). -/
def stepForsPackExpected (x : StepOpRowInputs) (firstJ count j : Nat) : Goldilocks :=
  (List.range count).foldl
    (fun acc sub =>
      if stRemPack + (firstJ + sub) / 6 = j then
        acc +ₚ (stepByteVal x sub *ₚ ‹2 ^ (8 * ((firstJ + sub) % 6))›)
      else acc)
    (x.prev j)

/-- Upper 28 bits of a 32-bit half of `leaf_global_idx`: digits `aux[2..16]`. -/
def stepHi28 (x : StepOpRowInputs) : Goldilocks :=
  stepWeightedSum (fun i => x.aux (2 + i)) (fun i => 4 ^ i) 14

/-- `expected_next[j]` of `StatelessDecompLimb { limb_idx = l }`. -/
def stepStatelessDecompExpected (x : StepOpRowInputs) (l j : Nat) : Goldilocks :=
  if l < 4 then stepForsPackExpected x (7 * l) 7 j
  else if l = 4 then stepForsPackExpected x 28 4 j
  else if l = 5 then
    (if j = stKpIdx then Goldilocks.add (x.aux 0) (Goldilocks.mul (x.aux 1) (Goldilocks.ofNat 4))
     else if j = stTreeLo then stepHi28 x
     else x.prev j)
  else if l = 6 then
    (if j = stTreeLo then Goldilocks.add (x.prev stTreeLo)
         (Goldilocks.mul (Goldilocks.add (x.aux 0) (Goldilocks.mul (x.aux 1) (Goldilocks.ofNat 4)))
           (Goldilocks.ofNat (2 ^ 28)))
     else if j = stTreeHi then stepHi28 x
     else x.prev j)
  else x.prev j

/-- `expected_next[j]` of `HmsgDecompLimb { limb_idx = l }`: the remaining-step counts
    `3 - d_r` packed two bits per chain, and the running digit sum. -/
def stepHmsgDecompExpected (x : StepOpRowInputs) (l j : Nat) : Goldilocks :=
  if j = stAccOrU1 then
    x.prev stAccOrU1 +ₚ stepPlainSum x.aux (if l < 4 then 31 else 4)
  else
    (List.range (if l < 4 then 31 else 4)).foldl
      (fun acc i =>
        if stRemPack + wotsPackSlot (31 * l + i) = j then
          acc +ₚ ((‹3› -ₚ x.aux i) *ₚ
            ‹2 ^ (2 * (31 * l + i - wotsPackSlotStart (wotsPackSlot (31 * l + i))))›)
        else acc)
      (x.prev j)

/-- Second sponge block of a 2-block Merkle node: `st_in = sub_sponge + [node, 1, IV, 0, ..]`. -/
def stepMerkleBlockBInput (x : StepOpRowInputs) : List Goldilocks :=
  (List.range 4).map (fun i => x.stIn i -ₚ (x.prev (stSubSponge + i) +ₚ x.prev (stWork + i))) ++
  [x.stIn 4 -ₚ (x.prev (stSubSponge + 4) +ₚ Goldilocks.one),
   x.stIn 5 -ₚ (x.prev (stSubSponge + 5) +ₚ poseidon2IvTag)] ++
  (List.range 6).map (fun i => x.stIn (6 + i) -ₚ x.prev (stSubSponge + 6 + i))

/-- First sponge block of a 2-block Merkle node with direction bit `aux[0]`, parent index
    `aux[1]`, sibling `aux[2..6]` and address limb `meta0`. -/
def stepMerkleBlockA (x : StepOpRowInputs) (domainTag meta0 : Goldilocks) : List Goldilocks :=
  [stepBoolCheck (x.aux 0), x.prev stCursorIdx -ₚ ((x.aux 0 +ₚ x.aux 1) +ₚ x.aux 1)] ++
  (List.range 4).flatMap (fun i =>
    [x.stIn i -ₚ x.pkSeed i,
     x.stIn (4 + i) -ₚ
       (((Goldilocks.one -ₚ x.aux 0) *ₚ x.prev (stWork + i)) +ₚ (x.aux 0 *ₚ x.aux (2 + i))),
     x.next (stWork + i) -ₚ
       ((x.aux 0 *ₚ x.prev (stWork + i)) +ₚ ((Goldilocks.one -ₚ x.aux 0) *ₚ x.aux (2 + i)))]) ++
  [x.stIn 8 -ₚ domainTag, x.stIn 9 -ₚ meta0, x.stIn 10 -ₚ x.prev stTreeLo,
   x.stIn 11 -ₚ x.prev stTreeHi] ++
  stepNextIsPerm x stSubSponge 12 ++
  [x.next stCursorIdx -ₚ x.aux 1] ++
  stepCarryUnchanged x
    (fun j => stepInBlock stSubSponge 12 j || stepInBlock stWork 4 j || j == stCursorIdx)

/-- Absorb `st_in = main_sponge + [blockA, blockB, 0]`. -/
def stepSpongeAbsorbInput (x : StepOpRowInputs) (blockA blockB : Nat → Goldilocks) :
    List Goldilocks :=
  (List.range 4).flatMap (fun i =>
    [x.stIn i -ₚ (x.prev (stMainSponge + i) +ₚ blockA i),
     x.stIn (4 + i) -ₚ (x.prev (stMainSponge + 4 + i) +ₚ blockB i),
     x.stIn (8 + i) -ₚ x.prev (stMainSponge + 8 + i)])

/-- Final squeeze `st_in = main_sponge + [1, 0, ..]`. -/
def stepSqueezeInput (x : StepOpRowInputs) : List Goldilocks :=
  [x.stIn 0 -ₚ (x.prev stMainSponge +ₚ Goldilocks.one)] ++
  (List.range 11).map (fun i => x.stIn (1 + i) -ₚ x.prev (stMainSponge + 1 + i))

/-- One WOTS+C chain step hashing `cur` under the address limb `step_c0 + kp_idx * 2^16`. -/
def stepWotsStepInput (x : StepOpRowInputs) (c0 : Goldilocks) : List Goldilocks :=
  [x.stIn 8 -ₚ domainWotsStep, x.stIn 9 -ₚ (c0 +ₚ (x.prev stKpIdx *ₚ ‹2 ^ 16›)),
   x.stIn 10 -ₚ x.prev stTreeLo, x.stIn 11 -ₚ x.prev stTreeHi]

/-- `eval_single_op_constraints_generic`: the transition constraints of one opcode class, in
    emission order. Every entry has degree at most 7 in the row cells. -/
def stepOpConstraints (kind : StepConstraintKind) (c0 : Goldilocks) (x : StepOpRowInputs) :
    List Goldilocks :=
  match kind with
  | .idle => (List.range 44).map x.next
  | .statefulHmsgBlock0 =>
    (List.range 6).map (fun i => stepBoolCheck (x.aux i)) ++
    (List.range 32).map (fun i => stepBoolCheck (x.aux (6 + i))) ++
    (List.range 4).flatMap (fun i =>
      [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i,
       x.next (stCurRoot + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgStateful,
     x.stIn 9 -ₚ ((stepWeightedSum x.aux (fun i => 2 ^ i) 6 *ₚ ‹2 ^ 32›) +ₚ
       stepWeightedSum (fun i => x.aux (6 + i)) (fun i => 2 ^ i) 32),
     x.stIn 10 -ₚ x.mu 4, x.stIn 11 -ₚ poseidon2IvTag,
     x.next stKpIdx -ₚ stepWeightedSum x.aux (fun i => 2 ^ i) 6] ++
    stepNextIsPerm x stMainSponge 12 ++
    stepZeroElsewhere x
      (fun j => stepInBlock stCurRoot 4 j || j == stKpIdx || stepInBlock stMainSponge 12 j)
  | .statefulHmsgBlock1 =>
    stepSpongeAbsorbInput x x.aux x.mu ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .statefulHmsgSqueeze =>
    stepSqueezeInput x ++
    stepNextIsPerm x stMainSponge 12 ++
    (List.range 6).map (fun s => x.next (stRemPack + s)) ++
    [x.next stAccOrU1] ++
    stepCarryUnchanged x
      (fun j => stepInBlock stRemPack 6 j || stepInBlock stMainSponge 12 j || j == stAccOrU1)
  | .statelessDeriveBlock0 =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgStateless, x.stIn 9 -ₚ x.mu 4, x.stIn 10,
     x.stIn 11 -ₚ poseidon2IvTag] ++
    stepNextIsPerm x stMainSponge 12 ++
    stepZeroElsewhere x (fun j => stepInBlock stMainSponge 12 j)
  | .statelessDeriveBlock1 =>
    stepSpongeAbsorbInput x x.aux x.mu ++
    stepNextIsPerm x stMainSponge 12 ++
    (List.range 6).map (fun s => x.next (stRemPack + s)) ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j || stepInBlock stRemPack 6 j)
  | .statelessDecompLimb l =>
    stepLimb63Decomp x l ++
    (List.range 44).map (fun j => x.next j -ₚ stepStatelessDecompExpected x l j)
  | .forsRootsSpongeInit =>
    (List.range 4).map (fun i => x.stIn i -ₚ x.pkSeed i) ++
    [x.stIn 4 -ₚ x.prev stKpIdx, x.stIn 5 -ₚ x.prev stTreeLo, x.stIn 6 -ₚ x.prev stTreeHi,
     x.stIn 7 -ₚ ‹32›, x.stIn 8 -ₚ domainForsRoots, x.stIn 9, x.stIn 10,
     x.stIn 11 -ₚ poseidon2IvTag] ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .forsLeafHash slot =>
    (List.range 4).map (fun k => quarticBase4 (x.aux (4 + k))) ++
    [x.prev (stRemPack + slot) -ₚ
       (stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4 +ₚ (x.aux 8 *ₚ ‹256›)),
     x.next (stRemPack + slot) -ₚ x.aux 8] ++
    (List.range 4).flatMap (fun i =>
      [x.stIn i -ₚ x.aux i, x.stIn (4 + i) -ₚ x.pkSeed i,
       x.next (stWork + i) -ₚ
         (x.permOut i +ₚ ((x.aux i +ₚ (‹2› *ₚ x.stIn (4 + i))) +ₚ (‹4› *ₚ x.stIn (8 + i))))]) ++
    [x.stIn 8 -ₚ domainForsLeaf,
     x.stIn 9 -ₚ ((x.prev stKpIdx *ₚ ‹2 ^ 24›) +ₚ
       (c0 +ₚ stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4)),
     x.stIn 10 -ₚ x.prev stTreeLo, x.stIn 11 -ₚ x.prev stTreeHi,
     x.next stCursorIdx -ₚ stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4] ++
    stepCarryUnchanged x
      (fun j => j == stRemPack + slot || stepInBlock stWork 4 j || j == stCursorIdx)
  | .forsMerkleBlockA =>
    stepMerkleBlockA x domainForsNode ((c0 +ₚ (x.prev stKpIdx *ₚ ‹2 ^ 16›)) +ₚ x.aux 1)
  | .forsMerkleBlockB isTreeLast isOddTree =>
    stepMerkleBlockBInput x ++
    (if isTreeLast then [x.prev stCursorIdx] else []) ++
    (if isTreeLast && !isOddTree then
      stepNextIsPerm x stCurRoot 4 ++ stepCarryUnchanged x (fun j => stepInBlock stCurRoot 4 j)
     else
      stepNextIsPerm x stWork 4 ++ stepCarryUnchanged x (fun j => stepInBlock stWork 4 j))
  | .forsRootsPairAbsorb isLastPair =>
    (if isLastPair then (List.range 6).map (fun s => x.prev (stRemPack + s)) else []) ++
    stepSpongeAbsorbInput x (fun i => x.prev (stCurRoot + i)) (fun i => x.prev (stWork + i)) ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .forsRootsFinalSqueeze =>
    stepSqueezeInput x ++
    stepNextIsPerm x stCurRoot 4 ++
    stepCarryUnchanged x (fun j => stepInBlock stCurRoot 4 j)
  | .detTreeHmsgBlock0 =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgDetTree, x.stIn 9 -ₚ (c0 +ₚ x.prev stKpIdx),
     x.stIn 10 -ₚ x.prev stTreeLo, x.stIn 11 -ₚ x.prev stTreeHi] ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .detTreeHmsgBlock1 =>
    (List.range 32).map (fun i => stepBoolCheck (x.aux i)) ++
    (List.range 4).map (fun i =>
      x.stIn i -ₚ (x.prev (stMainSponge + i) +ₚ x.prev (stCurRoot + i))) ++
    [x.stIn 4 -ₚ (x.prev (stMainSponge + 4) +ₚ stepWeightedSum x.aux (fun i => 2 ^ i) 32),
     x.stIn 5 -ₚ (x.prev (stMainSponge + 5) +ₚ Goldilocks.one)] ++
    (List.range 6).map (fun i => x.stIn (6 + i) -ₚ x.prev (stMainSponge + 6 + i)) ++
    stepNextIsPerm x stMainSponge 12 ++
    (List.range 6).map (fun s => x.next (stRemPack + s)) ++
    [x.next stAccOrU1] ++
    stepCarryUnchanged x
      (fun j => stepInBlock stRemPack 6 j || stepInBlock stMainSponge 12 j || j == stAccOrU1)
  | .hmsgDecompLimb l =>
    stepLimb63Decomp x l ++
    (if l = 4 then [stepHmsgDecompExpected x l stAccOrU1 -ₚ ‹192›] else []) ++
    (List.range 44).map (fun j => x.next j -ₚ stepHmsgDecompExpected x l j)
  | .wotsTellInit =>
    (List.range 4).map (fun i => x.stIn i -ₚ x.pkSeed i) ++
    [x.stIn 4 -ₚ (c0 +ₚ x.prev stKpIdx), x.stIn 5 -ₚ x.prev stTreeLo,
     x.stIn 6 -ₚ x.prev stTreeHi, x.stIn 7 -ₚ ‹128›, x.stIn 8 -ₚ domainWotsPk, x.stIn 9,
     x.stIn 10, x.stIn 11 -ₚ poseidon2IvTag] ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .wotsChainStep0 slot =>
    [stepBoolCheck (x.aux 4), stepBoolCheck (x.aux 5), stepBoolCheck (x.aux 6),
     x.aux 5 *ₚ (Goldilocks.one -ₚ x.aux 4), x.aux 6 *ₚ (Goldilocks.one -ₚ x.aux 5),
     x.prev (stRemPack + slot) -ₚ
       ((‹3› -ₚ ((x.aux 4 +ₚ x.aux 5) +ₚ x.aux 6)) +ₚ (x.aux 7 *ₚ ‹4›)),
     x.next (stRemPack + slot) -ₚ x.aux 7] ++
    (List.range 4).flatMap (fun i =>
      [x.stIn i -ₚ x.aux i, x.stIn (4 + i) -ₚ x.pkSeed i,
       x.next (stWork + i) -ₚ
         ((x.aux 4 *ₚ x.aux i) +ₚ ((Goldilocks.one -ₚ x.aux 4) *ₚ
           (x.permOut i +ₚ ((x.aux i +ₚ (‹2› *ₚ x.stIn (4 + i))) +ₚ (‹4› *ₚ x.stIn (8 + i))))))]) ++
    stepWotsStepInput x c0 ++
    [x.next stAccOrU1 -ₚ x.aux 5, x.next stWotsU2 -ₚ x.aux 6] ++
    stepCarryUnchanged x
      (fun j => j == stRemPack + slot || stepInBlock stWork 4 j || j == stAccOrU1 ||
        j == stWotsU2)
  | .wotsChainStep1 =>
    (List.range 4).flatMap (fun i =>
      [x.stIn i -ₚ x.prev (stWork + i), x.stIn (4 + i) -ₚ x.pkSeed i,
       x.next (stWork + i) -ₚ
         ((x.prev stAccOrU1 *ₚ x.prev (stWork + i)) +ₚ
           ((Goldilocks.one -ₚ x.prev stAccOrU1) *ₚ
             (x.permOut i +ₚ ((x.prev (stWork + i) +ₚ (‹2› *ₚ x.stIn (4 + i))) +ₚ
               (‹4› *ₚ x.stIn (8 + i))))))]) ++
    stepWotsStepInput x c0 ++
    stepCarryUnchanged x (fun j => stepInBlock stWork 4 j)
  | .wotsChainStep2 isOdd =>
    (List.range 4).flatMap (fun i =>
      [x.stIn i -ₚ x.prev (stWork + i), x.stIn (4 + i) -ₚ x.pkSeed i,
       x.next ((if isOdd then stWork else stSubSponge) + i) -ₚ
         ((x.prev stWotsU2 *ₚ x.prev (stWork + i)) +ₚ
           ((Goldilocks.one -ₚ x.prev stWotsU2) *ₚ
             (x.permOut i +ₚ ((x.prev (stWork + i) +ₚ (‹2› *ₚ x.stIn (4 + i))) +ₚ
               (‹4› *ₚ x.stIn (8 + i))))))]) ++
    stepWotsStepInput x c0 ++
    stepCarryUnchanged x (fun j => stepInBlock (if isOdd then stWork else stSubSponge) 4 j)
  | .wotsTellPairAbsorb isLastPair =>
    (if isLastPair then (List.range 5).map (fun s => x.prev (stRemPack + s)) else []) ++
    stepSpongeAbsorbInput x (fun i => x.prev (stSubSponge + i)) (fun i => x.prev (stWork + i)) ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .wotsTellFinalSqueeze =>
    stepSqueezeInput x ++
    stepNextIsPerm x stWork 4 ++
    [x.next stCursorIdx -ₚ x.prev stKpIdx] ++
    stepCarryUnchanged x (fun j => stepInBlock stWork 4 j || j == stCursorIdx)
  | .xmssMerkleBlockA =>
    stepMerkleBlockA x domainMerkleNode (c0 +ₚ x.aux 1)
  | .xmssMerkleBlockB isLayerLast isTopFinal =>
    stepMerkleBlockBInput x ++
    (if !isLayerLast then
      stepNextIsPerm x stWork 4 ++ stepCarryUnchanged x (fun j => stepInBlock stWork 4 j)
     else if isTopFinal then
      [x.prev stCursorIdx] ++
      (List.range 4).map (fun i => x.permOut i -ₚ x.pkRoot i) ++
      (List.range 44).map x.next
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
           (stepWeightedSum (fun i => x.aux (20 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›))] ++
      stepNextIsPerm x stCurRoot 4 ++
      [x.next stKpIdx -ₚ stepWeightedSum x.aux (fun i => 2 ^ i) 4,
       x.next stTreeLo -ₚ
         (stepWeightedSum (fun i => x.aux (4 + i)) (fun i => 4 ^ i) 14 +ₚ
           (stepWeightedSum (fun i => x.aux (18 + i)) (fun i => 4 ^ i) 2 *ₚ ‹2 ^ 28›)),
       x.next stTreeHi -ₚ stepWeightedSum (fun i => x.aux (20 + i)) (fun i => 4 ^ i) 14] ++
      stepCarryUnchanged x
        (fun j => stepInBlock stCurRoot 4 j || j == stKpIdx || j == stTreeLo || j == stTreeHi))

/-- Group A (`eval_group_a_and_boundaries_generic`): the recomputed `Poseidon2` output of the
    row and the 118 S-box residuals `(lane + rc)^7 - sbox_out`, each of degree 7. -/
def stepOpPermTrace (row : StepOpRow) : Poseidon2State12 × List Goldilocks :=
  let r1 := extRoundsResiduals poseidon2InitialExtConsts (applyME row.stIn) row.initExtSbox
  let r2 := intRoundsResiduals poseidon2InternalConsts r1.1 row.intSbox
  let r3 := extRoundsResiduals poseidon2TerminalExtConsts r2.1 row.termExtSbox
  (r3.1, r1.2 ++ r2.2 ++ r3.2)

/-- **Group A exactness.** If the S-box residuals of a row vanish, its recomputed permutation
    output is `poseidon2Perm12` of its `COL_ST_IN` block. -/
theorem stepOp256_groupA_exact (row : StepOpRow)
    (h : allZeroGoldilocks (stepOpPermTrace row).2 = true) :
    (stepOpPermTrace row).1 = poseidon2Perm12 row.stIn := by
  have hKey : poseidon2PermResiduals
      { input := row.stIn, initExtSbox := row.initExtSbox, intSbox := row.intSbox,
        termExtSbox := row.termExtSbox, output := (stepOpPermTrace row).1 } =
      (stepOpPermTrace row).2 ++
        (state12Sub (stepOpPermTrace row).1 (stepOpPermTrace row).1).toList := rfl
  have hZ : allZeroGoldilocks (poseidon2PermResiduals
      { input := row.stIn, initExtSbox := row.initExtSbox, intSbox := row.intSbox,
        termExtSbox := row.termExtSbox, output := (stepOpPermTrace row).1 }) = true := by
    rw [hKey, allZeroGoldilocks_append, Bool.and_eq_true]
    exact ⟨h, (state12Sub_toList_allZero_iff _ _).mpr rfl⟩
  exact poseidon2PermResiduals_output_eq hZ

/-- Boundary constraints of row `t` of a signer block of `rowsPerSigner` rows: the first row
    has `prev = 0` and the last row has `next = 0`, for active and inactive slots alike. -/
def stepOpBoundaryResiduals (rowsPerSigner t : Nat) (row : StepOpRow) : List Goldilocks :=
  (List.range 44).flatMap fun j =>
    [if t = 0 then row.prevState.getD j Goldilocks.zero else Goldilocks.zero,
     if t + 1 = rowsPerSigner then row.nextState.getD j Goldilocks.zero else Goldilocks.zero]

/-- Public inputs of one signer slot `(pk, mu)`; `none` is an inactive (blinding) slot, whose
    opcode selectors are all gated off. -/
abbrev StepOpSlot : Type := Option (AggValidatorPk × Digest5)

/-- The values the opcode constraints of a row read. -/
theorem stepOpPermTrace_nextState (row : StepOpRow) (next : List Goldilocks) :
    stepOpPermTrace { row with nextState := next } = stepOpPermTrace row := by rfl

@[expose] def stepOpRowInputs (pub : AggValidatorPk × Digest5) (row : StepOpRow) : StepOpRowInputs where
  prev    := fun j => row.prevState.getD j Goldilocks.zero
  next    := fun j => row.nextState.getD j Goldilocks.zero
  aux     := fun i => row.aux.getD i Goldilocks.zero
  stIn    := fun i => row.stIn.toList.getD i Goldilocks.zero
  permOut := fun i => (stepOpPermTrace row).1.toList.getD i Goldilocks.zero
  pkSeed  := fun i => pub.1.pkSeed.toList.getD i Goldilocks.zero
  pkRoot  := fun i => pub.1.pkRoot.toList.getD i Goldilocks.zero
  mu      := fun i =>
    [pub.2.limb0, pub.2.limb1, pub.2.limb2, pub.2.limb3, pub.2.limb4].getD i Goldilocks.zero

/-- All intra-row constraints of row `t` of a signer block: Group A, the boundary constraints,
    and, for an active slot, the transition constraints of the opcode scheduled at `t`. -/
def stepOp256RowResiduals (profile : AggSigProfile) (slot : StepOpSlot) (t : Nat)
    (row : StepOpRow) : List Goldilocks :=
  (stepOpPermTrace row).2 ++
  stepOpBoundaryResiduals (stepOpRowsPerSigner profile) t row ++
  match slot with
  | none => []
  | some pub =>
    stepOpConstraints (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1
      (Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).2)
      (stepOpRowInputs pub row)

/-- Intra-row constraints of the rows from global index `g` on: row `g` belongs to slot
    `g / rows_per_signer` at step `g % rows_per_signer`. -/
def stepOp256IntraResidualsFrom (profile : AggSigProfile) (slots : List StepOpSlot) :
    Nat → List StepOpRow → List Goldilocks
  | _, [] => []
  | g, row :: rest =>
    stepOp256RowResiduals profile (slots.getD (g / stepOpRowsPerSigner profile) none)
      (g % stepOpRowsPerSigner profile) row ++
    stepOp256IntraResidualsFrom profile slots (g + 1) rest

/-- Inter-row shift constraints between two consecutive rows: `NEXT_STATE` of the first equals
    `PREV_STATE` of the second, limb by limb. They are not gated by any selector. -/
def stepOpShiftResiduals (row rowNext : StepOpRow) : List Goldilocks :=
  (List.range 44).map fun j =>
    row.nextState.getD j Goldilocks.zero -ₚ rowNext.prevState.getD j Goldilocks.zero

/-- Inter-row shift constraints of a table: one block per `r` with `r + 1 < T`. -/
def stepOp256ShiftResiduals : List StepOpRow → List Goldilocks
  | r :: r' :: rest => stepOpShiftResiduals r r' ++ stepOp256ShiftResiduals (r' :: rest)
  | _ => []

/-- A table of `slots.length * rows_per_signer` well-shaped rows on which every intra-row
    constraint and every inter-row shift constraint vanishes. -/
def stepOp256TableOk (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) : Bool :=
  decide (0 < slots.length) &&
  decide (rows.length = slots.length * stepOpRowsPerSigner profile) &&
  rows.all StepOpRow.wellShaped &&
  allZeroGoldilocks (stepOp256IntraResidualsFrom profile slots 0 rows) &&
  allZeroGoldilocks (stepOp256ShiftResiduals rows)

/-- Project an intra-row constraint block from the flat residual stream. -/
theorem stepOp256IntraResidualsFrom_row_at (profile : AggSigProfile) (slots : List StepOpSlot) :
    ∀ (rows : List StepOpRow) (g i : Nat) (row : StepOpRow),
      rows[i]? = some row →
      allZeroGoldilocks (stepOp256IntraResidualsFrom profile slots g rows) = true →
      allZeroGoldilocks (stepOp256RowResiduals profile
        (slots.getD ((g + i) / stepOpRowsPerSigner profile) none)
        ((g + i) % stepOpRowsPerSigner profile) row) = true
  | [], _, _, _, h, _ => by simp at h
  | r :: rs, g, 0, row, h, hz => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst row
    rw [stepOp256IntraResidualsFrom, allZeroGoldilocks_append, Bool.and_eq_true] at hz
    simpa only [Nat.add_zero] using hz.1
  | r :: rs, g, i + 1, row, h, hz => by
    rw [stepOp256IntraResidualsFrom, allZeroGoldilocks_append, Bool.and_eq_true] at hz
    have hr := stepOp256IntraResidualsFrom_row_at profile slots rs (g + 1) i row h hz.2
    simpa only [Nat.add_right_comm g 1 i, Nat.add_assoc] using hr

/-- Every row of a valid table satisfies its actual scheduled constraint block. -/
theorem stepOp256TableOk_row_at (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) (i : Nat) (row : StepOpRow)
    (h : stepOp256TableOk profile slots rows = true) (hi : rows[i]? = some row) :
    allZeroGoldilocks (stepOp256RowResiduals profile
      (slots.getD (i / stepOpRowsPerSigner profile) none)
      (i % stepOpRowsPerSigner profile) row) = true := by
  unfold stepOp256TableOk at h
  simp only [Bool.and_eq_true] at h
  simpa only [Nat.zero_add] using
    stepOp256IntraResidualsFrom_row_at profile slots rows 0 i row hi h.1.2

/-- The shift constraints between two rows vanish exactly when the state is handed over. -/
theorem stepOp256_shift_iff (r r' : StepOpRow) :
    allZeroGoldilocks (stepOpShiftResiduals r r') = true ↔
      ∀ j, j < 44 →
        r.nextState.getD j Goldilocks.zero = r'.prevState.getD j Goldilocks.zero := by
  unfold stepOpShiftResiduals allZeroGoldilocks
  rw [List.all_map, List.all_eq_true]
  constructor
  · intro h j hj
    exact (sub_eq_zero_iff_goldilocks _ _).mp (h j (List.mem_range.mpr hj))
  · intro h j hj
    exact (sub_eq_zero_iff_goldilocks _ _).mpr (h j (List.mem_range.mp hj))

/-- On a table whose shift constraints vanish, every pair of consecutive rows hands over its
    44 state limbs. -/
theorem stepOp256_shift_links_rows :
    ∀ (rows : List StepOpRow) (g : Nat) (r r' : StepOpRow),
      rows[g]? = some r → rows[g + 1]? = some r' →
      allZeroGoldilocks (stepOp256ShiftResiduals rows) = true →
      ∀ j, j < 44 →
        r.nextState.getD j Goldilocks.zero = r'.prevState.getD j Goldilocks.zero
  | [], _, _, _, h, _, _ => absurd h (by simp)
  | [_], _, _, _, _, h', _ => absurd h' (by simp)
  | r0 :: r1 :: rest, 0, r, r', h, h', hz => by
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h h'
    subst h h'
    unfold stepOp256ShiftResiduals at hz
    rw [allZeroGoldilocks_append, Bool.and_eq_true] at hz
    exact (stepOp256_shift_iff r0 r1).mp hz.1
  | r0 :: r1 :: rest, g + 1, r, r', h, h', hz => by
    simp only [List.getElem?_cons_succ] at h h'
    unfold stepOp256ShiftResiduals at hz
    rw [allZeroGoldilocks_append, Bool.and_eq_true] at hz
    exact stepOp256_shift_links_rows (r1 :: rest) g r r' h h' hz.2

/-- Pointwise completeness as well as soundness of the intra-row residual stream.
    The offset is retained so this also applies to a block inside a larger table. -/
theorem stepOp256IntraResidualsFrom_iff (profile : AggSigProfile) (slots : List StepOpSlot) :
    ∀ (rows : List StepOpRow) (g : Nat),
      allZeroGoldilocks (stepOp256IntraResidualsFrom profile slots g rows) = true ↔
      ∀ (i : Nat) (row : StepOpRow), rows[i]? = some row →
        allZeroGoldilocks (stepOp256RowResiduals profile
          (slots.getD ((g + i) / stepOpRowsPerSigner profile) none)
          ((g + i) % stepOpRowsPerSigner profile) row) = true
  | [], _ => by simp [stepOp256IntraResidualsFrom, allZeroGoldilocks]
  | r :: rs, g => by
    constructor
    · exact fun h i row hi => stepOp256IntraResidualsFrom_row_at profile slots _ g i row hi h
    · intro h
      rw [stepOp256IntraResidualsFrom, allZeroGoldilocks_append, Bool.and_eq_true]
      refine ⟨?_, (stepOp256IntraResidualsFrom_iff profile slots rs (g + 1)).mpr ?_⟩
      · simpa only [Nat.add_zero] using h 0 r rfl
      · intro i row hi
        have hr := h (i + 1) row (by simpa only [List.getElem?_cons_succ] using hi)
        simpa only [Nat.add_right_comm g 1 i, Nat.add_assoc] using hr

/-- The entire shift stream vanishes exactly when every adjacent pair hands over all
    44 limbs. This converse permits constructing tables from executions, including
    transitions across signer-block boundaries. -/
theorem stepOp256ShiftResiduals_iff :
    ∀ (rows : List StepOpRow),
      allZeroGoldilocks (stepOp256ShiftResiduals rows) = true ↔
      ∀ (i : Nat) (r r' : StepOpRow), rows[i]? = some r → rows[i + 1]? = some r' →
        ∀ j < 44, r.nextState.getD j Goldilocks.zero = r'.prevState.getD j Goldilocks.zero
  | [] => by simp [stepOp256ShiftResiduals, allZeroGoldilocks]
  | [r] => by simp [stepOp256ShiftResiduals, allZeroGoldilocks]
  | r :: r' :: rest => by
    constructor
    · exact fun h i a b ha hb => stepOp256_shift_links_rows _ i a b ha hb h
    · intro h
      rw [stepOp256ShiftResiduals, allZeroGoldilocks_append, Bool.and_eq_true]
      refine ⟨(stepOp256_shift_iff r r').mpr (h 0 r r' rfl rfl),
        (stepOp256ShiftResiduals_iff (r' :: rest)).mpr ?_⟩
      intro i a b ha hb
      exact h (i + 1) a b ha hb

/-- Both boundary gates are necessary and sufficient; no condition is imposed on an
    interior row by the boundary residuals. -/
theorem stepOpBoundaryResiduals_iff (rowsPerSigner t : Nat) (row : StepOpRow) :
    allZeroGoldilocks (stepOpBoundaryResiduals rowsPerSigner t row) = true ↔
      (∀ j < 44, t = 0 → row.prevState.getD j Goldilocks.zero = Goldilocks.zero) ∧
      (∀ j < 44, t + 1 = rowsPerSigner →
        row.nextState.getD j Goldilocks.zero = Goldilocks.zero) := by
  unfold stepOpBoundaryResiduals allZeroGoldilocks
  simp only [List.all_flatMap, List.all_eq_true, List.mem_range, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  by_cases hFirst : t = 0 <;> by_cases hLast : t + 1 = rowsPerSigner <;>
    simp [hFirst, hLast, forall_and]

/-- A pointwise interface to the original 256-column table checker. All actual rows,
    including active slots, must satisfy their scheduled gate, and all adjacent rows
    must agree. Neither a signature-verifier premise nor a surrogate table is used. -/
theorem stepOp256TableOk_iff_rows (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) :
    stepOp256TableOk profile slots rows = true ↔
      0 < slots.length ∧
      rows.length = slots.length * stepOpRowsPerSigner profile ∧
      (∀ row ∈ rows, row.wellShaped = true) ∧
      (∀ (i : Nat) (row : StepOpRow), rows[i]? = some row →
        allZeroGoldilocks (stepOp256RowResiduals profile
          (slots.getD (i / stepOpRowsPerSigner profile) none)
          (i % stepOpRowsPerSigner profile) row) = true) ∧
      (∀ (i : Nat) (r r' : StepOpRow), rows[i]? = some r → rows[i + 1]? = some r' →
        ∀ j < 44, r.nextState.getD j Goldilocks.zero = r'.prevState.getD j Goldilocks.zero) := by
  unfold stepOp256TableOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    stepOp256IntraResidualsFrom_iff, stepOp256ShiftResiduals_iff, Nat.zero_add, and_assoc]


theorem exists_ne_zero_of_not_allZero :
    ∀ (l : List Goldilocks), allZeroGoldilocks l = false →
      ∃ c, c ∈ l ∧ c ≠ Goldilocks.zero
  | [], h => absurd h (by decide)
  | c :: rest, h => by
    by_cases hc : c = Goldilocks.zero
    · have hb : (Goldilocks.zero == Goldilocks.zero) = true := by decide
      have hr : allZeroGoldilocks rest = false := by
        unfold allZeroGoldilocks at h ⊢
        rw [List.all_cons, hc, hb, Bool.true_and] at h
        exact h
      obtain ⟨c', hm, hne⟩ := exists_ne_zero_of_not_allZero rest hr
      exact ⟨c', List.mem_cons_of_mem _ hm, hne⟩
    · exact ⟨c, List.mem_cons_self .., hc⟩

private theorem filter_length_le_of_imp {α : Type} (p q : α → Bool)
    (h : ∀ a, p a = true → q a = true) :
    ∀ (l : List α), (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := filter_length_le_of_imp p q h l
    cases hp : p a
    · cases hq : q a
      · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte]
        exact ih
      · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        exact Nat.le_succ_of_le ih
    · have hq := h a hp
      simp only [List.filter_cons, hp, hq, ↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ ih

private theorem filter_or_length_le {α : Type} (p q : α → Bool) :
    ∀ (l : List α),
      (l.filter (fun a => p a || q a)).length ≤ (l.filter p).length + (l.filter q).length
  | [] => Nat.le_refl 0
  | a :: l => by
    have ih := filter_or_length_le p q l
    cases hp : p a <;> cases hq : q a <;>
      simp only [List.filter_cons, hp, hq, Bool.or_self, Bool.or_true,
        Bool.or_false, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;>
      omega

private theorem filter_eq_length_zero_of_not_mem {α : Type} [DecidableEq α] (z : α) :
    ∀ (l : List α), z ∉ l → (l.filter (fun a => decide (a = z))).length = 0
  | [], _ => rfl
  | a :: l, h => by
    have hne : a ≠ z := fun e => h (List.mem_cons.mpr (Or.inl e.symm))
    have hd : decide (a = z) = false := decide_eq_false hne
    have hl : z ∉ l := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [List.filter_cons, hd]
    exact filter_eq_length_zero_of_not_mem z l hl

private theorem nodup_filter_eq_length_le_one {α : Type} [DecidableEq α] (z : α) :
    ∀ (l : List α), l.Nodup → (l.filter (fun a => decide (a = z))).length ≤ 1
  | [], _ => Nat.zero_le 1
  | a :: l, hnd => by
    have hnd' := List.nodup_cons.mp hnd
    by_cases ha : a = z
    · have h0 := filter_eq_length_zero_of_not_mem z l (ha ▸ hnd'.1)
      have hd : decide (a = z) = true := decide_eq_true ha
      rw [List.filter_cons, hd]
      exact Nat.le_of_eq (congrArg Nat.succ h0)
    · have hd : decide (a = z) = false := decide_eq_false ha
      rw [List.filter_cons, hd]
      exact nodup_filter_eq_length_le_one z l hnd'.2


/-! #### Random-`tau` root counting -/


/-! #### `#tooth` rows -/

theorem getD_replicate_zero :
    ∀ (n j : Nat),
      (List.replicate n Goldilocks.zero).getD j Goldilocks.zero = Goldilocks.zero
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, j + 1 => getD_replicate_zero n j

/-- A row whose `Poseidon2` columns are the honest trace of the all-zero input, with carried
    state `prevState`, zero `NEXT_STATE` and auxiliary cells `aux` (unconstrained on `Idle` and
    inactive rows, where `populate_inactive_signer_rows` places the blinding limbs). -/
def stepOpIdleRow (prevState aux : List Goldilocks) : StepOpRow where
  stIn        := state12Zero
  initExtSbox := (honestPoseidon2PermWitness state12Zero).initExtSbox
  intSbox     := (honestPoseidon2PermWitness state12Zero).intSbox
  termExtSbox := (honestPoseidon2PermWitness state12Zero).termExtSbox
  prevState   := prevState
  nextState   := List.replicate 44 Goldilocks.zero
  aux         := aux

/-- The all-zero row: every one of the 256 cells is zero. -/
def stepOpZeroRow : StepOpRow where
  stIn        := state12Zero
  initExtSbox := List.replicate 4 state12Zero
  intSbox     := List.replicate 22 Goldilocks.zero
  termExtSbox := List.replicate 4 state12Zero
  prevState   := List.replicate 44 Goldilocks.zero
  nextState   := List.replicate 44 Goldilocks.zero
  aux         := List.replicate 38 Goldilocks.zero

private theorem stepOpIdleRow_groupA (prevState aux : List Goldilocks) :
    allZeroGoldilocks (stepOpPermTrace (stepOpIdleRow prevState aux)).2 = true := by
  have hKey : poseidon2PermResiduals (honestPoseidon2PermWitness state12Zero) =
      (stepOpPermTrace (stepOpIdleRow prevState aux)).2 ++
        (state12Sub (stepOpPermTrace (stepOpIdleRow prevState aux)).1
          (honestPoseidon2PermWitness state12Zero).output).toList := rfl
  have hZ := (poseidon2PermResiduals_allZero_iff (honestPoseidon2PermWitness state12Zero)).mpr rfl
  rw [hKey, allZeroGoldilocks_append, Bool.and_eq_true] at hZ
  exact hZ.1

private theorem allZero_zero_pairs :
    allZeroGoldilocks
      ((List.range 44).flatMap fun _ => [Goldilocks.zero, Goldilocks.zero]) = true := by
  decide

private theorem stepOpIdleRow_boundary (rowsPerSigner t : Nat) (prevState aux : List Goldilocks)
    (hP : t = 0 → prevState = List.replicate 44 Goldilocks.zero) :
    allZeroGoldilocks (stepOpBoundaryResiduals rowsPerSigner t (stepOpIdleRow prevState aux)) =
      true := by
  have hEq : stepOpBoundaryResiduals rowsPerSigner t (stepOpIdleRow prevState aux) =
      (List.range 44).flatMap fun _ => [Goldilocks.zero, Goldilocks.zero] := by
    unfold stepOpBoundaryResiduals stepOpIdleRow
    congr 1
    funext j
    by_cases ht : t = 0
    · simp only [ht, hP ht, ↓reduceIte, getD_replicate_zero, ite_self]
    · simp only [ht, ↓reduceIte, getD_replicate_zero, ite_self]
  rw [hEq]
  exact allZero_zero_pairs

private theorem allZero_zero_map :
    allZeroGoldilocks ((List.range 44).map fun _ => Goldilocks.zero) = true := by
  decide

/-- An `Idle` row passes every intra-row gate of an active slot at any step scheduled as
    `Idle`, whatever state it claims to have received (other than on the first row). -/
theorem stepOpIdleRow_intra_ok (profile : AggSigProfile) (pub : AggValidatorPk × Digest5)
    (t : Nat) (prevState aux : List Goldilocks)
    (hOp : (buildSignerProgram profile).getD t StepOp.idle = StepOp.idle)
    (hP : t = 0 → prevState = List.replicate 44 Goldilocks.zero) :
    allZeroGoldilocks
      (stepOp256RowResiduals profile (some pub) t (stepOpIdleRow prevState aux)) = true := by
  unfold stepOp256RowResiduals
  rw [allZeroGoldilocks_append, allZeroGoldilocks_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨stepOpIdleRow_groupA prevState aux, stepOpIdleRow_boundary _ t prevState aux hP⟩, ?_⟩
  rw [hOp]
  have hEq : stepOpConstraints (stepOpKindAndC0 StepOp.idle).1
      (Goldilocks.ofNat (stepOpKindAndC0 StepOp.idle).2)
      (stepOpRowInputs pub (stepOpIdleRow prevState aux)) =
      (List.range 44).map fun _ => Goldilocks.zero := by
    show (List.range 44).map
      (fun j => (List.replicate 44 Goldilocks.zero).getD j Goldilocks.zero) = _
    congr 1
    funext j
    exact getD_replicate_zero 44 j
  have hZ := allZero_zero_map
  rw [← hEq] at hZ
  exact hZ


private theorem buildRoundsSboxPoly_length {RC ST SB : Type}
    (sboxFn : RC → ST → SB) (nextFn : ST → SB → ST) :
    ∀ (rcs : List RC) (cur : ST),
      (buildRoundsSboxPoly sboxFn nextFn rcs cur).length = rcs.length
  | [], _ => rfl
  | rc :: rcs, cur => by
    simp only [buildRoundsSboxPoly, List.length_cons, buildRoundsSboxPoly_length sboxFn nextFn rcs]

private theorem honestZeroPerm_sbox_lengths :
    (honestPoseidon2PermWitness state12Zero).initExtSbox.length = 4 ∧
    (honestPoseidon2PermWitness state12Zero).intSbox.length = 22 ∧
    (honestPoseidon2PermWitness state12Zero).termExtSbox.length = 4 := by
  simp only [honestPoseidon2PermWitness, buildExtRoundsSbox, buildIntRoundsSbox,
    buildRoundsSboxPoly_length, poseidon2InitialExtConsts_length,
    poseidon2InternalConsts_length, poseidon2TerminalExtConsts_length] <;> simp

/-- An `Idle` row with 44 carried limbs and 38 auxiliary cells has the 256-column shape. -/
theorem stepOpIdleRow_wellShaped (prevState aux : List Goldilocks)
    (hP : prevState.length = 44) (hA : aux.length = 38) :
    (stepOpIdleRow prevState aux).wellShaped = true := by
  obtain ⟨h1, h2, h3⟩ := honestZeroPerm_sbox_lengths
  unfold StepOpRow.wellShaped stepOpIdleRow
  simp only [h1, h2, h3, hP, hA, List.length_replicate, beq_self_eq_true, Bool.and_self]

private theorem getD_replicate_none {α : Type} :
    ∀ (k i : Nat), (List.replicate k (none : Option α)).getD i none = none
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | k + 1, i + 1 => getD_replicate_none k i

private theorem all_replicate_of {α : Type} (f : α → Bool) (a : α) (h : f a = true) :
    ∀ (n : Nat), (List.replicate n a).all f = true
  | 0 => rfl
  | n + 1 => Bool.and_eq_true_iff.mpr ⟨h, all_replicate_of f a h n⟩

private theorem stepOpInactive_intra (profile : AggSigProfile) (k : Nat) (aux : List Goldilocks) :
    ∀ (n g : Nat),
      allZeroGoldilocks (stepOp256IntraResidualsFrom profile (List.replicate k none) g
        (List.replicate n (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux))) = true
  | 0, _ => rfl
  | n + 1, g => by
    show allZeroGoldilocks
      (stepOp256RowResiduals profile
          ((List.replicate k none).getD (g / stepOpRowsPerSigner profile) none)
          (g % stepOpRowsPerSigner profile)
          (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux) ++
        stepOp256IntraResidualsFrom profile (List.replicate k none) (g + 1)
          (List.replicate n (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux))) = true
    rw [allZeroGoldilocks_append, Bool.and_eq_true, getD_replicate_none]
    refine ⟨?_, stepOpInactive_intra profile k aux n (g + 1)⟩
    unfold stepOp256RowResiduals
    rw [allZeroGoldilocks_append, allZeroGoldilocks_append, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨stepOpIdleRow_groupA _ aux, stepOpIdleRow_boundary _ _ _ aux (fun _ => rfl)⟩, rfl⟩

private theorem stepOpInactive_shift (aux : List Goldilocks) :
    ∀ (n : Nat),
      allZeroGoldilocks (stepOp256ShiftResiduals
        (List.replicate n (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux))) = true
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    show allZeroGoldilocks
      (stepOpShiftResiduals (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux)
          (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux) ++
        stepOp256ShiftResiduals
          (List.replicate (n + 1) (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux))) = true
    rw [allZeroGoldilocks_append, Bool.and_eq_true]
    exact ⟨(stepOp256_shift_iff _ _).mpr (fun _ _ => rfl), stepOpInactive_shift aux (n + 1)⟩

/-- **Completeness for inactive slots (`populate_inactive_signer_rows`).** A table of `k ≥ 1`
    inactive slots filled with `Idle` rows (honest `Poseidon2` trace of the zero input, zero
    carried state, arbitrary auxiliary cells) satisfies every intra-row and inter-row
    constraint. In particular `stepOp256TableOk` is satisfiable. -/
theorem stepOp256_inactive_table_complete (profile : AggSigProfile) (k : Nat) (hk : 0 < k)
    (aux : List Goldilocks) (hA : aux.length = 38) :
    stepOp256TableOk profile (List.replicate k none)
      (List.replicate (k * stepOpRowsPerSigner profile)
        (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux)) = true := by
  unfold stepOp256TableOk
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact decide_eq_true (by rw [List.length_replicate]; exact hk)
  · exact decide_eq_true (by rw [List.length_replicate, List.length_replicate])
  · exact all_replicate_of _ _
      (stepOpIdleRow_wellShaped _ aux List.length_replicate hA) _
  · exact stepOpInactive_intra profile k aux _ 0
  · exact stepOpInactive_shift aux _

private theorem stepOpZeroRow_groupA :
    allZeroGoldilocks (stepOpPermTrace stepOpZeroRow).2 = false := by
  cases h : allZeroGoldilocks (stepOpPermTrace stepOpZeroRow).2 with
  | false => rfl
  | true =>
    apply False.elim
    apply first_external_zero_trace_rejected (stepOpPermTrace stepOpZeroRow).1
    have he : poseidon2PermResiduals
        { input := state12Zero, initExtSbox := List.replicate 4 state12Zero,
          intSbox := List.replicate 22 Goldilocks.zero,
          termExtSbox := List.replicate 4 state12Zero, output := (stepOpPermTrace stepOpZeroRow).1 } =
        (stepOpPermTrace stepOpZeroRow).2 ++
          (state12Sub (stepOpPermTrace stepOpZeroRow).1 (stepOpPermTrace stepOpZeroRow).1).toList := rfl
    rw [he, allZeroGoldilocks_append, h]
    exact (state12Sub_toList_allZero_iff _ _).mpr rfl

/-- **`#tooth`: all-zero rows are rejected.** For every profile, every slot assignment and
    every row count `n`, the table of `n` all-zero rows is rejected: with `n = 0` the row count
    is wrong, and with `n > 0` the Group A S-box constraints of the first row fail, since
    `(0 + rc)^7 ≠ 0`. -/
theorem tooth_stepOp256_zero_rows_rejected (profile : AggSigProfile) (slots : List StepOpSlot)
    (n : Nat) :
    stepOp256TableOk profile slots (List.replicate n stepOpZeroRow) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  unfold stepOp256TableOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hPos, hLen⟩, _⟩, hIntra⟩, _⟩ := h
  cases n with
  | zero =>
    rw [List.replicate_zero, List.length_nil] at hLen
    cases profile <;> simp only [stepOpRowsPerSigner] at hLen <;> omega
  | succ m =>
    rw [List.replicate_succ] at hIntra
    unfold stepOp256IntraResidualsFrom stepOp256RowResiduals at hIntra
    rw [allZeroGoldilocks_append, allZeroGoldilocks_append, allZeroGoldilocks_append,
      Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hIntra
    rw [stepOpZeroRow_groupA] at hIntra
    exact absurd hIntra.1.1.1 (by decide)

end StepOpTable

end Qsag

end

public section

namespace Qsag

/-- Valid index ranges of parameterized `StepConstraintKind` constructors (`trace.rs`). -/
def StepConstraintKind.validSlot : StepConstraintKind → Bool
  | .statelessDecompLimb l => decide (l < 7)
  | .forsLeafHash slot     => decide (slot < 6)
  | .hmsgDecompLimb l      => decide (l < 5)
  | .wotsChainStep0 slot   => decide (slot < 5)
  | _                      => true

/-- Complete duplicate-free catalog of all 52 `StepConstraintKind` classes of the deployed machine. -/
def allStepConstraintKinds : List StepConstraintKind :=
  [.idle, .statefulHmsgBlock0, .statefulHmsgBlock1, .statefulHmsgSqueeze,
   .statelessDeriveBlock0, .statelessDeriveBlock1] ++
  (List.range 7).map StepConstraintKind.statelessDecompLimb ++
  [.forsRootsSpongeInit] ++
  (List.range 6).map StepConstraintKind.forsLeafHash ++
  [.forsMerkleBlockA,
   .forsMerkleBlockB false false, .forsMerkleBlockB false true,
   .forsMerkleBlockB true false, .forsMerkleBlockB true true,
   .forsRootsPairAbsorb false, .forsRootsPairAbsorb true,
   .forsRootsFinalSqueeze,
   .detTreeHmsgBlock0, .detTreeHmsgBlock1] ++
  (List.range 5).map StepConstraintKind.hmsgDecompLimb ++
  [.wotsTellInit] ++
  (List.range 5).map StepConstraintKind.wotsChainStep0 ++
  [.wotsChainStep1,
   .wotsChainStep2 false, .wotsChainStep2 true,
   .wotsTellPairAbsorb false, .wotsTellPairAbsorb true,
   .wotsTellFinalSqueeze,
   .xmssMerkleBlockA,
   .xmssMerkleBlockB false false, .xmssMerkleBlockB false true,
   .xmssMerkleBlockB true false, .xmssMerkleBlockB true true]

theorem allStepConstraintKinds_nodup : allStepConstraintKinds.Nodup := by
  decide +kernel

theorem allStepConstraintKinds_validSlot :
    ∀ k ∈ allStepConstraintKinds, k.validSlot = true := by
  decide +kernel

private theorem mem_allStepConstraintKinds_of_validSlot (k : StepConstraintKind)
    (h : k.validSlot = true) : k ∈ allStepConstraintKinds := by
  cases k with
  | idle | statefulHmsgBlock0 | statefulHmsgBlock1 | statefulHmsgSqueeze
  | statelessDeriveBlock0 | statelessDeriveBlock1 | forsRootsSpongeInit
  | forsMerkleBlockA | forsRootsFinalSqueeze | detTreeHmsgBlock0 | detTreeHmsgBlock1
  | wotsTellInit | wotsChainStep1 | wotsTellFinalSqueeze | xmssMerkleBlockA =>
    decide +kernel
  | forsMerkleBlockB a b => cases a <;> cases b <;> decide +kernel
  | forsRootsPairAbsorb a => cases a <;> decide +kernel
  | wotsChainStep2 a => cases a <;> decide +kernel
  | wotsTellPairAbsorb a => cases a <;> decide +kernel
  | xmssMerkleBlockB a b => cases a <;> cases b <;> decide +kernel
  | statelessDecompLimb l =>
    have hl : l < 7 := of_decide_eq_true h
    rcases l with _ | _ | _ | _ | _ | _ | _ | l <;> first | decide +kernel | omega
  | forsLeafHash slot =>
    have hs : slot < 6 := of_decide_eq_true h
    rcases slot with _ | _ | _ | _ | _ | _ | slot <;> first | decide +kernel | omega
  | hmsgDecompLimb l =>
    have hl : l < 5 := of_decide_eq_true h
    rcases l with _ | _ | _ | _ | _ | l <;> first | decide +kernel | omega
  | wotsChainStep0 slot =>
    have hs : slot < 5 := of_decide_eq_true h
    rcases slot with _ | _ | _ | _ | _ | slot <;> first | decide +kernel | omega

theorem wotsPackSlot_lt_5 (chain : Nat) : wotsPackSlot chain < 5 := by
  unfold wotsPackSlot
  split <;> try decide
  split <;> try decide
  split <;> try decide
  split <;> decide

private theorem pushLayerWotsAndMerkle_validSlot (layer subHeight : Nat) (isTopFinal : Bool) :
    ∀ op ∈ pushLayerWotsAndMerkle layer subHeight isTopFinal,
      (stepOpKindAndC0 op).1.validSlot = true := by
  intro op hMem
  unfold pushLayerWotsAndMerkle at hMem
  simp only [List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with ((rfl | ⟨pair, _, ⟨sub, _, rfl | rfl | rfl⟩ | rfl⟩) | rfl) | ⟨lvl, _, rfl | rfl⟩
  · rfl
  · unfold stepOpKindAndC0; exact decide_eq_true (wotsPackSlot_lt_5 _)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem signerProgramBody_validSlot (profile : AggSigProfile) :
    ∀ op ∈ signerProgramBody profile, (stepOpKindAndC0 op).1.validSlot = true := by
  intro op hMem
  cases profile with
  | xmssPoseidon2 =>
    unfold signerProgramBody at hMem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_range] at hMem
    rcases hMem with ((rfl | rfl | rfl) | ⟨l, hl, rfl⟩) | hPush
    · rfl
    · rfl
    · rfl
    · exact decide_eq_true hl
    · exact pushLayerWotsAndMerkle_validSlot 0 6 true op hPush
  | corduroyPoseidon2 =>
    unfold signerProgramBody at hMem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_flatMap, List.mem_range] at hMem
    rcases hMem with (((((rfl | rfl) | ⟨l, hl, rfl⟩) | rfl) | hFors) | rfl) | ⟨layer, _, hLayer⟩
    · rfl
    · rfl
    · exact decide_eq_true hl
    · rfl
    · rcases hFors with ⟨pair, hPair, ⟨sub, hSub, rfl | ⟨lvl, _, rfl | rfl⟩⟩ | rfl⟩
      · exact decide_eq_true (by omega : (2 * pair + sub) / 6 < 6)
      · rfl
      · rfl
      · rfl
    · rfl
    · rcases hLayer with ((rfl | rfl) | ⟨l, hl, rfl⟩) | hPush
      · rfl
      · rfl
      · exact decide_eq_true hl
      · exact pushLayerWotsAndMerkle_validSlot layer 4 (layer + 1 == 16) op hPush

theorem buildSignerProgram_kind_mem_and_valid (profile : AggSigProfile) (t : Nat) :
    (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1 ∈ allStepConstraintKinds ∧
    (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1.validSlot = true := by
  have hVal : (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1.validSlot = true := by
    by_cases ht : t < (buildSignerProgram profile).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
      have hMem := List.getElem_mem ht
      unfold buildSignerProgram at hMem
      rcases List.mem_append.mp hMem with hBody | hRep
      · exact signerProgramBody_validSlot profile _ hBody
      · have hIdle : (buildSignerProgram profile)[t] = StepOp.idle :=
          (List.mem_replicate.mp hRep).2
        rw [hIdle]; rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt ht), Option.getD_none]
      rfl
  exact ⟨mem_allStepConstraintKinds_of_validSlot _ hVal, hVal⟩


end Qsag

end

public section

namespace Qsag

theorem stepBoolCheck_eq (b : Goldilocks) :
    stepBoolCheck b = Goldilocks.mul b (Goldilocks.sub Goldilocks.one b) := by rfl
theorem stepWeightedSum_eq (f : Nat → Goldilocks) (w : Nat → Nat) (n : Nat) :
    stepWeightedSum f w n = (List.range n).foldl
      (fun acc i => Goldilocks.add acc (Goldilocks.mul (f i) (Goldilocks.ofNat (w i))))
      Goldilocks.zero := by rfl
theorem stepLimb63Decomp_eq (x : StepOpRowInputs) (l : Nat) :
    stepLimb63Decomp x l = (List.range 31).map (fun i => quarticBase4 (x.aux i)) ++
      [stepBoolCheck (x.aux 31), Goldilocks.sub (x.prev (stMainSponge + l))
        (Goldilocks.add (stepWeightedSum x.aux (fun i => 4 ^ i) 31)
          (Goldilocks.mul (x.aux 31) (Goldilocks.ofNat (2 ^ 62))))] := by rfl
theorem stepByteVal_eq (x : StepOpRowInputs) (sub : Nat) :
    stepByteVal x sub = Goldilocks.add
      (Goldilocks.add (Goldilocks.add (x.aux (4 * sub))
        (Goldilocks.mul (x.aux (4 * sub + 1)) (Goldilocks.ofNat 4)))
        (Goldilocks.mul (x.aux (4 * sub + 2)) (Goldilocks.ofNat 16)))
      (Goldilocks.mul (x.aux (4 * sub + 3)) (Goldilocks.ofNat 64)) := by rfl
theorem stepHi28_def (x : StepOpRowInputs) :
    stepHi28 x = stepWeightedSum (fun i => x.aux (2 + i)) (fun i => 4 ^ i) 14 := by rfl
end Qsag

end

public section

namespace Qsag

#export_eqns StepConstraintKind.validSlot
#export_eqns StepOpRow.wellShaped
#export_eqns buildSignerProgram
#export_eqns signerProgramBody
#export_eqns stAccOrU1
#export_eqns stCurRoot
#export_eqns stCursorIdx
#export_eqns stKpIdx
#export_eqns stMainSponge
#export_eqns stRemPack
#export_eqns stSubSponge
#export_eqns stTreeHi
#export_eqns stTreeLo
#export_eqns stWork
#export_eqns stWotsU2
#export_eqns stepCarryUnchanged
#export_eqns stepForsPackExpected
#export_eqns stepHmsgDecompExpected
#export_eqns stepInBlock
#export_eqns stepMerkleBlockA
#export_eqns stepMerkleBlockBInput
#export_eqns stepNextIsPerm
#export_eqns stepOp256IntraResidualsFrom
#export_eqns stepOp256RowResiduals
#export_eqns stepOp256TableOk
#export_eqns stepOpConstraints
#export_eqns stepOpKindAndC0
#export_eqns stepOpRowInputs
#export_eqns stepOpRowsPerSigner
#export_eqns stepPlainSum
#export_eqns stepSpongeAbsorbInput
#export_eqns stepSqueezeInput
#export_eqns stepStatelessDecompExpected
#export_eqns stepWotsStepInput
#export_eqns stepZeroElsewhere
#export_eqns wotsPackSlot
#export_eqns stepOpPermTrace stepOpBoundaryResiduals allStepConstraintKinds
/-! Selected computational equations consumed by the AIR-completeness proof. -/
theorem honestPoseidon2PermWitness_lengths (input : Poseidon2State12) :
    (honestPoseidon2PermWitness input).initExtSbox.length = 4 ∧
    (honestPoseidon2PermWitness input).intSbox.length = 22 ∧
    (honestPoseidon2PermWitness input).termExtSbox.length = 4 := by
  simp only [honestPoseidon2PermWitness, buildExtRoundsSbox, buildIntRoundsSbox,
    buildRoundsSboxPoly_length, poseidon2InitialExtConsts_length,
    poseidon2InternalConsts_length, poseidon2TerminalExtConsts_length] <;> simp

#export_eqns stepHi28
theorem stepStatelessDecompExpected_congr_next (x : StepOpRowInputs)
    (next' : Nat → Goldilocks) (l j : Nat) :
    stepStatelessDecompExpected { x with next := next' } l j =
      stepStatelessDecompExpected x l j := by rfl

theorem stepHmsgDecompExpected_congr_next (x : StepOpRowInputs)
    (next' : Nat → Goldilocks) (l j : Nat) :
    stepHmsgDecompExpected { x with next := next' } l j =
      stepHmsgDecompExpected x l j := by rfl

#export_eqns pushLayerWotsAndMerkle
/-- An Hmsg digit fold changes only its five remainder limbs and accumulator. -/
theorem stepHmsgDecompExpected_frame (x : StepOpRowInputs) (l j : Nat)
    (hj : j < 7 ∨ 12 ≤ j) (hacc : j ≠ 42) :
    stepHmsgDecompExpected x l j = x.prev j := by
  unfold stepHmsgDecompExpected
  simp only [stAccOrU1, hacc, ↓reduceIte]
  apply foldl_fixed_step
  intro i _
  have hs := wotsPackSlot_lt_5 (31 * l + i)
  have hn : stRemPack + wotsPackSlot (31 * l + i) ≠ j := by
    change 7 + wotsPackSlot (31 * l + i) ≠ j
    omega
  simp only [hn, ↓reduceIte]

/-- Packing up to 32 FORS indices changes only the six remainder limbs. -/
theorem stepForsPackExpected_frame (x : StepOpRowInputs) (firstJ count j : Nat)
    (hcount : firstJ + count ≤ 32) (hj : j < 7 ∨ 13 ≤ j) :
    stepForsPackExpected x firstJ count j = x.prev j := by
  unfold stepForsPackExpected
  apply foldl_fixed_step
  intro sub hsub
  have hs := List.mem_range.mp hsub
  have hn : stRemPack + (firstJ + sub) / 6 ≠ j := by
    change 7 + (firstJ + sub) / 6 ≠ j
    omega
  simp only [hn, ↓reduceIte]

/-- Stateless unpacking preserves every register outside address and remainder limbs. -/
theorem stepStatelessDecompExpected_frame (x : StepOpRowInputs) (l j : Nat)
    (hj : j < 4 ∨ 13 ≤ j) :
    stepStatelessDecompExpected x l j = x.prev j := by
  unfold stepStatelessDecompExpected
  by_cases hl : l < 4
  · simp only [hl, ↓reduceIte]
    exact stepForsPackExpected_frame x (7 * l) 7 j (by omega) (by omega)
  · simp only [hl, ↓reduceIte]
    by_cases h4 : l = 4
    · simp only [h4, ↓reduceIte]
      exact stepForsPackExpected_frame x 28 4 j (by decide) (by omega)
    · have hkp : j ≠ stKpIdx := by change j ≠ 4; omega
      have hlo : j ≠ stTreeLo := by change j ≠ 5; omega
      have hhi : j ≠ stTreeHi := by change j ≠ 6; omega
      simp only [h4, ↓reduceIte, hkp, hlo, hhi]
      split <;> first | rfl | (split <;> rfl)


/-! Exact finite accessors for the deployed padded signer program. -/
theorem stepXmssProgram_pairs : ∀ p < 64,
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p) .idle =
      .wotsChainStep0 0 (2 * p) (wotsPackSlot (2 * p)) ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 1) .idle = .wotsChainStep1 0 (2 * p) ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 2) .idle = .wotsChainStep2 0 (2 * p) false ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 3) .idle =
      .wotsChainStep0 0 (2 * p + 1) (wotsPackSlot (2 * p + 1)) ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 4) .idle = .wotsChainStep1 0 (2 * p + 1) ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 5) .idle = .wotsChainStep2 0 (2 * p + 1) true ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 6) .idle = .wotsTellPairAbsorb p := by
  decide +kernel

theorem buildSignerProgram_xmss_chains : ∀ c < 128,
    (buildSignerProgram .xmssPoseidon2).getD (8 + 1 + 7 * (c / 2) + 3 * (c % 2)) .idle =
      .wotsChainStep0 0 c (wotsPackSlot c) := by decide +kernel

theorem stepXmssProgram_merkle : ∀ l < 6,
    (buildSignerProgram .xmssPoseidon2).getD (458 + 2 * l) .idle = .xmssMerkleBlockA 0 l ∧
    (buildSignerProgram .xmssPoseidon2).getD (458 + 2 * l + 1) .idle =
      .xmssMerkleBlockB (l + 1 == 6) (l + 1 == 6) := by decide +kernel

theorem stepXmssProgram_idle : ∀ t < 512, 470 ≤ t →
    (buildSignerProgram .xmssPoseidon2).getD t .idle = .idle := by decide +kernel

theorem stepForwardProgram_last (profile : AggSigProfile) :
    (buildSignerProgram profile).getD (stepOpRowsPerSigner profile - 1) .idle = .idle := by
  cases profile <;> decide +kernel

theorem stepStatelessDecompExpected_five (x : StepOpRowInputs) (j : Nat) :
    stepStatelessDecompExpected x 5 j =
      (if j = stKpIdx then Goldilocks.add (x.aux 0) (Goldilocks.mul (x.aux 1) (Goldilocks.ofNat 4))
       else if j = stTreeLo then stepHi28 x else x.prev j) := by rfl

theorem stepStatelessDecompExpected_six (x : StepOpRowInputs) (j : Nat) :
    stepStatelessDecompExpected x 6 j =
      (if j = stTreeLo then Goldilocks.add (x.prev stTreeLo)
         (Goldilocks.mul (Goldilocks.add (x.aux 0) (Goldilocks.mul (x.aux 1) (Goldilocks.ofNat 4)))
           (Goldilocks.ofNat (2 ^ 28)))
       else if j = stTreeHi then stepHi28 x else x.prev j) := by rfl

theorem stepStatelessDecompExpected_pack_frame (x : StepOpRowInputs) (l j : Nat)
    (hl : l < 5) (hj : j < 7 ∨ 13 ≤ j) :
    stepStatelessDecompExpected x l j = x.prev j := by
  unfold stepStatelessDecompExpected
  by_cases h4 : l < 4
  · simp only [h4, ↓reduceIte]
    exact stepForsPackExpected_frame x (7 * l) 7 j (by omega) hj
  · have he : l = 4 := by omega
    simp only [he, ↓reduceIte]
    exact stepForsPackExpected_frame x 28 4 j (by decide) hj

theorem stepXmssProgram_decomp (l : Nat) (hl : l < 5) :
    (buildSignerProgram .xmssPoseidon2).getD (3 + l) .idle = .hmsgDecompLimb l := by
  rcases l with _ | _ | _ | _ | _ | l <;> first | rfl | omega

/-- Instruction classes used by the XMSS program. -/
def stepXmssSupported : StepOp → Bool
  | .idle | .statefulHmsgBlock0 | .statefulHmsgBlock1 | .statefulHmsgSqueeze
  | .hmsgDecompLimb _ | .wotsTellInit _ | .wotsChainStep0 _ _ _
  | .wotsChainStep1 _ _ | .wotsChainStep2 _ _ _ | .wotsTellPairAbsorb _
  | .wotsTellFinalSqueeze | .xmssMerkleBlockA _ _
  | .xmssMerkleBlockB false _ | .xmssMerkleBlockB true true => true
  | _ => false

theorem stepXmssProgram_supported :
    (buildSignerProgram .xmssPoseidon2).all stepXmssSupported = true := by
  decide +kernel


theorem stepXmssProgram_at_0 :
    (buildSignerProgram .xmssPoseidon2).getD 0 .idle = .statefulHmsgBlock0 := by rfl

theorem stepXmssProgram_at_1 :
    (buildSignerProgram .xmssPoseidon2).getD 1 .idle = .statefulHmsgBlock1 := by rfl

theorem stepXmssProgram_at_2 :
    (buildSignerProgram .xmssPoseidon2).getD 2 .idle = .statefulHmsgSqueeze := by rfl

theorem stepXmssProgram_at_8 :
    (buildSignerProgram .xmssPoseidon2).getD 8 .idle = .wotsTellInit 0 := by rfl

theorem wotsPackSlot_range0 : ∀ c < 128,
    wotsPackSlot c = 0 ↔ 0 ≤ c ∧ c < 0 + 26 := by decide +kernel

theorem wotsPackSlot_range1 : ∀ c < 128,
    wotsPackSlot c = 1 ↔ 26 ≤ c ∧ c < 26 + 26 := by decide +kernel

theorem wotsPackSlot_range2 : ∀ c < 128,
    wotsPackSlot c = 2 ↔ 52 ≤ c ∧ c < 52 + 26 := by decide +kernel

theorem wotsPackSlot_range3 : ∀ c < 128,
    wotsPackSlot c = 3 ↔ 78 ≤ c ∧ c < 78 + 25 := by decide +kernel

theorem wotsPackSlot_range4 : ∀ c < 128,
    wotsPackSlot c = 4 ↔ 103 ≤ c ∧ c < 103 + 25 := by decide +kernel

theorem stepXmssProgram_at_469 :
    (buildSignerProgram .xmssPoseidon2).getD 469 .idle = .xmssMerkleBlockB true true :=
  (stepXmssProgram_merkle 5 (by decide)).2

theorem signerProgramBody_xmss_last :
    (signerProgramBody .xmssPoseidon2)[469]? = some (.xmssMerkleBlockB true true) := by
  have hi : 469 < (signerProgramBody .xmssPoseidon2).length := by
    rw [buildSignerProgram_length.1]; decide
  have h := stepXmssProgram_at_469
  rw [buildSignerProgram.public_eqs, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi, List.getElem?_eq_getElem hi, Option.getD_some] at h
  rw [List.getElem?_eq_getElem hi, h]

/-- Skip the initial WOTS row and the 64 seven-row chain pairs when looking up a suffix row. -/
private theorem getElem?_after_wots_pairs (layer : Nat) (pairs : Nat → List StepOp)
    (h : ∀ p, (pairs p).length = 7) (tail : List StepOp) (i : Nat) :
    (([StepOp.wotsTellInit layer] ++ (List.range 64).flatMap pairs) ++ tail)[449 + i]? =
      tail[i]? := by
  have hlen : ([StepOp.wotsTellInit layer] ++ (List.range 64).flatMap pairs).length = 449 := by
    rw [List.length_append, List.length_flatMap]
    simp only [h, List.map_const', List.length_range, List.sum_replicate_nat]
    rfl
  rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
  simp

theorem pushLayerWotsAndMerkle_four_last (layer : Nat) (isTop : Bool) :
    (pushLayerWotsAndMerkle layer 4 isTop)[457]? =
      some (.xmssMerkleBlockB true isTop) := by
  rw [pushLayerWotsAndMerkle.public_eqs, List.append_assoc (_ ++ _)]
  exact (getElem?_after_wots_pairs layer _ (fun _ => rfl) _ 8).trans (by rfl)

#export_eqns wotsPackSlotStart
#export_eqns stepXmssSupported
theorem stepXmssProgram_at_457 :
    (buildSignerProgram .xmssPoseidon2).getD 457 .idle = .wotsTellFinalSqueeze := by
  have hi : 457 < (signerProgramBody .xmssPoseidon2).length := by
    rw [buildSignerProgram_length.1]; decide
  rw [buildSignerProgram.public_eqs, List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
    signerProgramBody.public_eqs.1, List.getElem?_append_right (by decide)]
  change ((pushLayerWotsAndMerkle 0 6 true)[449]?).getD .idle = _
  rw [pushLayerWotsAndMerkle.public_eqs, List.append_assoc (_ ++ _),
    show 449 = 449 + 0 from rfl, getElem?_after_wots_pairs _ _ (fun _ => rfl)]
  rfl

/-- Guard-independent append structure of the row checker, including an unknown slot. -/
theorem stepOp256RowResiduals_def (profile : AggSigProfile) (slot : StepOpSlot) (t : Nat)
    (row : StepOpRow) :
    stepOp256RowResiduals profile slot t row =
      (stepOpPermTrace row).2 ++
      stepOpBoundaryResiduals (stepOpRowsPerSigner profile) t row ++
      (match slot with
       | none => []
       | some pub =>
         stepOpConstraints (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1
           (Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).2)
           (stepOpRowInputs pub row)) := by rfl

end Qsag
end

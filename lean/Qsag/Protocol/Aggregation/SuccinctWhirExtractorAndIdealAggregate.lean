module
/- Packed-fiber WHIR verification, transcript extraction and aggregate refinement. -/

public import Qsag.Spec.Encoding
public import Qsag.Spec.IdealAggregate
public import Qsag.Spec.GameBound
public import Qsag.Spec.Refines
public import Qsag.Oracle.ProbPkgBridge
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Protocol.Aggregation.ClosedWhirSchedule
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness
public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
public import Qsag.Protocol.Aggregation.ZkHemV2ComposedZkAndCerts
public import Qsag.Protocol.Aggregation.QuinticMultiStageWhir
import Qsag.Tactic.AssuranceKit

public section
attribute [-instance] Fin.instLinearOrderPackage

namespace Qsag.SuccinctWhirAgg

open Qsag Qsag.ClosedFs Qsag.ClosedWhir Qsag.ZkHemV2Cert Qsag.ZkHemV2Packed

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 100000

local infixl:65 " +ᵍ " => CommRingOps.add
local infixl:65 " -ᵍ " => CommRingOps.sub
local infixl:70 " *ᵍ " => CommRingOps.mul

/-! ## §2. Unified `.xmssPoseidon2` & `.corduroyPoseidon2` `StepOp256` Committee Extraction -/

/-- Supported deployed hash-based validator signature profiles. -/
@[expose] def IsDeployedAggProfile (profile : AggSigProfile) : Prop :=
  profile = .xmssPoseidon2 ∨ profile = .corduroyPoseidon2

/-- Native signature geometry corresponding to `profile`. -/
@[expose] def profileGeom : AggSigProfile → AggSigGeometry
  | .xmssPoseidon2 => xmssPoseidon2Geom
  | .corduroyPoseidon2 => corduroyPoseidon2Geom

/-- Extract slot `slotIdx`'s native signature from `rows` for either `.xmssPoseidon2` or `.corduroyPoseidon2`. -/
@[expose] def extractSlotNativeSig (profile : AggSigProfile) (rows : List StepOpRow)
    (slotIdx : Nat) : AggNativeSignature :=
  match profile with
  | .xmssPoseidon2 => stepXmssSig (stepOpSlotRow .xmssPoseidon2 rows slotIdx)
  | .corduroyPoseidon2 => stepCordSig (stepOpSlotRow .corduroyPoseidon2 rows slotIdx)

/-- Public slot vector derived from an `AggregateStatement` for `stepOp256TableOk`. -/
@[expose] def succinctCommitteeSlots {nVal : Nat}
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) : List StepOpSlot :=
  (List.finRange nVal).map fun i =>
    if stmt.bitmap.getLsbD i.val then
      some (stmt.roster i, computeMessageMu (stmt.roster i) stmt.message)
    else
      none

private theorem finRange_getElem?_local (n k : Nat) (hk : k < n) :
    (List.finRange n)[k]? = some ⟨k, hk⟩ := by
  have hLen : (List.finRange n).length = n := List.length_finRange
  have hk' : k < (List.finRange n).length := by rw [hLen]; exact hk
  rw [List.getElem?_eq_getElem hk', List.getElem_finRange]
  rfl

theorem succinctCommitteeSlots_getElem? {nVal : Nat}
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (k : Nat) (hk : k < nVal) :
    (succinctCommitteeSlots stmt)[k]? =
      some (if stmt.bitmap.getLsbD k then
        some (stmt.roster ⟨k, hk⟩, computeMessageMu (stmt.roster ⟨k, hk⟩) stmt.message)
      else none) := by
  unfold succinctCommitteeSlots
  rw [List.getElem?_map, finRange_getElem?_local nVal k hk]
  rfl

/-- **Unified `.xmssPoseidon2` + `.corduroyPoseidon2` `StepOp256` Extraction (`stepOp256TableOk_bothProfiles_extract`):**
    Connects both `stepOp256TableOk_xmss_extract` and `stepOp256TableOk_corduroy_extract` to `Spec.ValidAggregateWitness`. -/
theorem stepOp256TableOk_bothProfiles_extract {nVal : Nat}
    (profile : AggSigProfile) (hDep : IsDeployedAggProfile profile)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal)
    (rows : List StepOpRow)
    (hProfAll : (List.finRange nVal).all (fun i =>
      !stmt.bitmap.getLsbD i.val || ((stmt.roster i).profile == profile)) = true)
    (hTable : stepOp256TableOk profile (succinctCommitteeSlots stmt) rows = true) :
    Spec.ValidAggregateWitness (verifyAggNativeSig (profileGeom profile)) stmt
      (fun i => some (extractSlotNativeSig profile rows i.val)) := by
  refine Spec.ValidAggregateWitness.intro (fun i hAct => ?_)
  refine ⟨extractSlotNativeSig profile rows i.val, rfl, ?_⟩
  have hProfMem := List.all_eq_true.mp hProfAll i (List.mem_finRange i)
  rw [hAct] at hProfMem
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hProfMem
  have hSlot : (succinctCommitteeSlots stmt)[i.val]? =
      some (some (stmt.roster i, computeMessageMu (stmt.roster i) stmt.message)) := by
    rw [succinctCommitteeSlots_getElem? stmt i.val i.isLt]
    have hFinEq : (⟨i.val, i.isLt⟩ : Fin nVal) = i := Fin.ext rfl
    rw [hFinEq, hAct]; simp only [↓reduceIte]
  rcases hDep with rfl | rfl
  · exact stepOp256TableOk_xmss_extract (succinctCommitteeSlots stmt) rows i.val
      (stmt.roster i, computeMessageMu (stmt.roster i) stmt.message) stmt.message
      hTable hSlot hProfMem rfl
  · exact stepOp256TableOk_corduroy_extract (succinctCommitteeSlots stmt) rows i.val
      (stmt.roster i, computeMessageMu (stmt.roster i) stmt.message) stmt.message
      hTable hSlot hProfMem rfl

/-- Single-slot `StepOp256` extraction for slot `i`'s isolated row slice `slotRows`. -/
theorem singleSlot_stepOp256_extract
    (profile : AggSigProfile) (hDep : IsDeployedAggProfile profile)
    (pk : AggValidatorPk) (msg : Spec.Bytes) (slotRows : List StepOpRow)
    (hProf : pk.profile = profile)
    (hTable : stepOp256TableOk profile [some (pk, computeMessageMu pk msg)] slotRows = true) :
    verifyAggNativeSig (profileGeom profile) pk msg (extractSlotNativeSig profile slotRows 0) = true := by
  have hSlot0 : ([some (pk, computeMessageMu pk msg)] : List StepOpSlot)[0]? =
      some (some (pk, computeMessageMu pk msg)) := rfl
  rcases hDep with rfl | rfl
  · exact stepOp256TableOk_xmss_extract _ slotRows 0 (pk, computeMessageMu pk msg) msg
      hTable hSlot0 hProf rfl
  · exact stepOp256TableOk_corduroy_extract _ slotRows 0 (pk, computeMessageMu pk msg) msg
      hTable hSlot0 hProf rfl

/-! ## §3. Salted slot leaves and the packed WHIR verifier -/

/-- Prefix-free codec framing salted Stage-0 slot execution rows `(salt, profile, slotIdx, slotRows)`
    into a single oracle query `Spec.Bytes` so `decodeSlotLeafSig` is statement- and key-independent. -/
structure SlotLeafTableCodec where
  encode : BitVec 256 → AggSigProfile → Nat → List StepOpRow → Spec.Bytes
  decode : Spec.Bytes → Option (BitVec 256 × AggSigProfile × Nat × List StepOpRow)
  decode_encode : ∀ salt prof idx rows,
    decode (encode salt prof idx rows) = some (salt, prof, idx, rows)

theorem SlotLeafTableCodec.encode_inj (c : SlotLeafTableCodec)
    {s1 s2 : BitVec 256} {p1 p2 : AggSigProfile} {i1 i2 : Nat} {r1 r2 : List StepOpRow}
    (h : c.encode s1 p1 i1 r1 = c.encode s2 p2 i2 r2) :
    s1 = s2 ∧ p1 = p2 ∧ i1 = i2 ∧ r1 = r2 := by
  have hd := congrArg c.decode h
  rw [c.decode_encode, c.decode_encode] at hd
  injection hd with hEq
  rcases Prod.mk.inj hEq with ⟨hs, hRest1⟩
  rcases Prod.mk.inj hRest1 with ⟨hp, hRest2⟩
  rcases Prod.mk.inj hRest2 with ⟨hi, hr⟩
  exact ⟨hs, hp, hi, hr⟩

/-- Statement-free, key-free single-query byte decoder extracting the native signature from a
    recorded Stage-0 slot-leaf preimage `b : Spec.Bytes`. -/
def decodeSlotLeafSig (slotC : SlotLeafTableCodec) (b : Spec.Bytes) : Option AggNativeSignature :=
  match slotC.decode b with
  | some (_, prof, _, slotRows) => some (extractSlotNativeSig prof slotRows 0)
  | none => none

theorem decodeSlotLeafSig_encode (slotC : SlotLeafTableCodec)
    (salt : BitVec 256) (prof : AggSigProfile) (idx : Nat) (slotRows : List StepOpRow) :
    decodeSlotLeafSig slotC (slotC.encode salt prof idx slotRows) =
      some (extractSlotNativeSig prof slotRows 0) := by
  unfold decodeSlotLeafSig
  rw [slotC.decode_encode]

abbrev PackedFiber := List QuinticGoldilocks
abbrev PackedRound := SuccinctRoundMsg Spec.Bytes (WhirPub QuinticGoldilocks)

/-- The initial oracle and each later commit-round oracle store one vector per fiber. -/
abbrev PackedStmt := QuinticGoldilocks × (Nat → PackedFiber)
abbrev PackedMsg := WhirPub QuinticGoldilocks × (Nat → Nat → PackedFiber)

def packedQueries (env : WhirEnv QuinticGoldilocks) (stages : List WhirStage)
    (tr : List (WhirPub QuinticGoldilocks × Nat)) : List (Nat × Nat) :=
  match splitStages stages tr with
  | none => []
  | some views =>
    (List.range stages.length).flatMap fun i =>
      match stages[i]?, views[i]? with
      | some st, some v => (List.range st.queryCount).map fun j =>
          (i, env.chalPos v.answer.2 j st.domainSize)
      | _, _ => []

private theorem packedQueries_stage_lt (env : WhirEnv QuinticGoldilocks)
    (stages : List WhirStage) (tr : List (WhirPub QuinticGoldilocks × Nat)) (q : Nat × Nat)
    (hq : q ∈ packedQueries env stages tr) : q.1 < stages.length := by
  unfold packedQueries at hq
  split at hq
  · cases hq
  · obtain ⟨i, hi, hq⟩ := List.mem_flatMap.mp hq
    split at hq
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
      exact List.mem_range.mp hi
    · cases hq

/-- Reconstruct the scalar stage-zero table in antipodal (strided fiber) order. -/
def unpackInitial (stages : List WhirStage) (x : PackedStmt) : WhirStmt QuinticGoldilocks :=
  match stages with
  | [] => ⟨[], x.1⟩
  | st :: _ => ⟨(List.range (2 ^ st.foldK * st.domainSize)).map
      (fun p => (x.2 (p % st.domainSize)).getD (p / st.domainSize) QuinticGoldilocks.zero), x.1⟩

/-- Detect a single pair of distinct candidate polynomials that agrees at
    every OOD point extracted from the packed round challenge. -/
def packedOodCollision (ps : List (GsUniPoly QuinticGoldilocks)) (c : Nat) : Bool :=
  ps.any fun p => ps.any fun q => decide (p.coeffs ≠ q.coeffs) &&
    (List.range 5).all fun j => decide (RoundPoly.evalCoeffs p.coeffs (whirField c j) =
      RoundPoly.evalCoeffs q.coeffs (whirField c j))

private theorem packedOod_first {ps : List (GsUniPoly QuinticGoldilocks)} {c : Nat}
    (hit : packedOodCollision ps c = true) : gsListHasOodCollision ps (whirField c 0) = true := by
  obtain ⟨p,hp,h⟩ := List.any_eq_true.mp hit
  obtain ⟨q,hq,b⟩ := List.any_eq_true.mp h
  obtain ⟨ne,all⟩ := Bool.and_eq_true_iff.mp b
  exact gsListHasOodCollision_of_pair _ p q hp hq (fun eq => of_decide_eq_true ne (congrArg _ eq))
    _ (of_decide_eq_true (List.all_eq_true.mp all 0 (by decide)))

private theorem packedOod_upper (hi N : Nat) (width : N = 2^hi * 2^400) (ps : List (GsUniPoly QuinticGoldilocks)) (B : Nat)
    (bound : qsum (2^400) (fun c => if gsListHasOodCollision ps (decodeQuintic400 c.val) then 1 else 0) ≤ B) :
    qsum N (fun c => if packedOodCollision ps c.val then 1 else 0) ≤ 2^hi * B := by
  let score := fun z => if gsListHasOodCollision ps z then 1 else 0
  calc
    _ ≤ qsum N (fun c => score (whirField c.val 0)) := by
      apply qsum_le_qsum
      intro c
      by_cases h : packedOodCollision ps c.val = true
      · simp [score,h,packedOod_first h]
      · simp [h]
    _ = _ := qsum_mul_mod_eq width (Nat.two_pow_pos 400) _ (fun t => score (decodeQuintic400 t))
      (fun c => congrArg score (whirField_first c.val))
    _ ≤ _ := Nat.mul_le_mul_left _ bound

private theorem scaled400 {hi bad B : Nat} (h : bad ≤ 2^hi * B) (hB : B * 2^277 < 2^400) :
    bad * 2^277 < 2^hi * 2^400 := by
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h)
    (by rw [Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_left hB (Nat.two_pow_pos _))

private theorem seedMassPos {N : Nat} (event : Fin N → Bool) (a : Fin N) (yes : event a = true) :
    0 < qsum N (fun i => if event i then 1 else 0) := by
  calc
    1 = qsum N (fun i => if i = a then 1 else 0) := (qsum_eq_indicator _ _).symm
    _ ≤ _ := by
      apply qsum_le_qsum
      intro i
      by_cases eq : i = a
      · subst i; simp [yes]
      · simp [eq]

private theorem packedOod_word (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) (st : WhirStage)
    (first : (zkHemV2ProdSched n).stages.head? = some st) (shift : QuinticGoldilocks)
    (nz : shift ≠ CommRingOps.zero) (seed : Nat) :
    ∃ word : QuinticGoldilocks → QuinticGoldilocks, packedOodCollision
      (gsDecodeList st.degBound st.agree (ZkHemV2.fiberRoots st.logDomain shift) word) seed = true := by
  let env := {zkHemV2QuinticEnv with chalField := fun _ j => whirField seed j}
  obtain ⟨word,p,hp,q,hq,ne,hit⟩ := deployed_first_ood_list_collision n lo hi st first shift nz env ⟨0,Nat.two_pow_pos _⟩
  refine ⟨word,?_⟩
  apply List.any_eq_true.mpr
  refine ⟨p,hp,List.any_eq_true.mpr ⟨q,hq,Bool.and_eq_true_iff.mpr ⟨decide_eq_true ?_,?_⟩⟩⟩
  · intro eq; exact ne (UPoly.ext eq)
  · exact List.all_eq_true.mpr fun j mem => decide_eq_true (hit ⟨j,List.mem_range.mp mem⟩)

private theorem packedOod_bound (n extra N : Nat) (hN : 0 < N)
    (width : N = 2^extra * 2^400) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : WhirStage) (first : (zkHemV2ProdSched n).stages.head? = some st)
    (shift : QuinticGoldilocks) (nz : shift ≠ CommRingOps.zero)
    (word : QuinticGoldilocks → QuinticGoldilocks) :
    let ps := gsDecodeList st.degBound st.agree (ZkHemV2.fiberRoots st.logDomain shift) word
    RatBound.lt ⟨qsum N (fun c => if packedOodCollision ps c.val then 1 else 0),N,hN⟩ (RatBound.invPow2 277) := by
  intro ps
  have mem : st ∈ (packedProdSched n).stages := by
    change st ∈ packedProdStages n
    rw [packedProdStages_eq n lo hi]
    rw [zkHemV2ProdSched.public_eqs] at first
    exact List.mem_of_mem_head? first
  obtain ⟨_,_,bound,lt⟩ := deployed_single_ood_gs_bad_lt_277 n lo hi st mem shift nz word
  change _ * 2^277 < 1 * N
  change (singleOodSeedBound st).num * 2^277 < 1 * 2^400 at lt
  rw [Nat.one_mul] at lt ⊢
  exact Nat.lt_of_lt_of_eq (scaled400 (hi := extra) (packedOod_upper extra N width ps _ bound) lt) width.symm

/-- Any received word fixed before the full packed squeeze has probability
    below 2^-277 of a decode-list pair agreeing at all five first-stage OOD points. -/
theorem packed_first_ood_collision_lt_277 (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : WhirStage) (first : (zkHemV2ProdSched n).stages.head? = some st)
    (shift : QuinticGoldilocks) (nz : shift ≠ CommRingOps.zero) (word : QuinticGoldilocks → QuinticGoldilocks) :
    let ps := gsDecodeList st.degBound st.agree (ZkHemV2.fiberRoots st.logDomain shift) word
    let bad := qsum (2^packedChallengeBits) fun c => if packedOodCollision ps c.val then 1 else 0
    RatBound.lt ⟨bad,2^packedChallengeBits,Nat.two_pow_pos _⟩ (RatBound.invPow2 277) :=
  packedOod_bound n (packedChallengeBits - 400) _ (Nat.two_pow_pos _)
    (Nat.pow_add 2 (packedChallengeBits - 400) 400) lo hi st first shift nz word

/-- For the verifier's full squeeze, the same two decoded polynomials agree on
    all five OOD coordinates with a positive probability below 2^-277. -/
theorem packed_first_ood_positive_mass (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : WhirStage) (first : (zkHemV2ProdSched n).stages.head? = some st)
    (shift : QuinticGoldilocks) (nz : shift ≠ CommRingOps.zero) (seed : Fin (2^packedChallengeBits)) :
    ∃ word : QuinticGoldilocks → QuinticGoldilocks,
      let ps := gsDecodeList st.degBound st.agree (ZkHemV2.fiberRoots st.logDomain shift) word
      let bad := qsum (2^packedChallengeBits) fun c => if packedOodCollision ps c.val then 1 else 0
      0 < bad ∧ RatBound.lt ⟨bad,2^packedChallengeBits,Nat.two_pow_pos _⟩ (RatBound.invPow2 277) := by
  obtain ⟨word,hit⟩ := packedOod_word n lo hi st first shift nz seed.val
  exact ⟨word,seedMassPos _ seed hit,packed_first_ood_collision_lt_277 n lo hi st first shift nz word⟩

#verify_constructive packed_first_ood_collision_lt_277 packed_first_ood_positive_mass

@[expose] def packedWhirIop (logCells : Nat) :
    OracleIop PackedStmt QuinticGoldilocks PackedMsg (WhirPub QuinticGoldilocks)
      PackedFiber (packedProdSched logCells).numRounds where
  w := packedChallengeBits
  pubStmt := Prod.fst
  pubMsg := Prod.fst
  inLang := fun x => whirInLang (packedQuinticWhirEnv logCells) (packedProdSched logCells)
    (unpackInitial (packedProdStages logCells) x)
  depth := packedStageDepth (packedProdStages logCells)
  table := fun x ms i pos => match i with
    | 0 => x.2 pos
    | j + 1 => (ms[commitRoundIdx (packedProdStages logCells) j]?).elim []
        (fun m => m.2 (j + 1) pos)
  queries := fun _ => packedQueries (packedQuinticWhirEnv logCells) (packedProdStages logCells)
  verdict := fun claim tr fibers =>
    let qs := packedQueries (packedQuinticWhirEnv logCells) (packedProdStages logCells) tr
    decide (qs.length = fibers.length) &&
    (qs.zip fibers).all (fun (q, f) =>
      ((packedProdStages logCells)[q.1]?).any fun st => f.length == 2 ^ st.foldK) &&
    whirVerdict (packedQuinticWhirEnv logCells) (packedProdSched logCells) claim tr fibers.flatten

def packedBridge (logCells : Nat) : SuccinctIopBridge (packedWhirIop logCells) Spec.Bytes where
  rootsOf := fun r0 ms i => match i with
    | 0 => r0 0
    | j + 1 => (ms[commitRoundIdx (packedProdStages logCells) j]?).bind (·.root) |>.getD []
  liftStmt := fun claim r0 tbl => (claim, tbl 0 (r0 0))
  liftMsg := fun _ sm tbl => (sm.pub, fun i => tbl i (sm.root.getD []))
  pubStmt_lift := fun _ _ _ => rfl
  pubMsg_lift := fun _ _ _ => rfl
  table_lift := by
    intro ps r0 str tbl q hlen hq _
    have hstage := packedQueries_stage_lt _ _ _ q hq
    rcases q with ⟨_ | j, pos⟩
    · rfl
    · have hj : j < (packedProdStages logCells).length := by dsimp only at hstage; omega
      have hr : commitRoundIdx (packedProdStages logCells) j < (str.map Prod.fst).length := by
        rw [List.length_map, hlen]
        exact commitRoundIdx_lt_roundsOf _ j hj
      simp only [packedWhirIop, liftMsgsAux_getElem?, List.getElem?_eq_getElem hr,
        Nat.zero_add, Option.map_some, Option.elim_some, Option.bind_some]

/-- Wire proof. Each opening contains one packed fiber and one Merkle path. -/
structure SuccinctWhirAggregateProof where
  salt : BitVec 256
  slotCommitRoot : Spec.Bytes
  whirRoot0 : Spec.Bytes
  claim : QuinticGoldilocks
  rounds : List PackedRound
  canopyOpenings : List (PackedFiber × List Spec.Bytes)
  contextDigest : Spec.Bytes

@[expose] def succinctWhirProofSigs (_ : SuccinctWhirAggregateProof) : List AggNativeSignature := []

structure WhirFsContext where
  logCells : Nat
  profile : AggSigProfile
  roster : List AggValidatorPk
  bitmap : Nat
  message : Spec.Bytes
  salt : BitVec 256
  slotRoot : Spec.Bytes
  whirRoot : Spec.Bytes
  claim : QuinticGoldilocks

structure SuccinctWhirByteFraming where
  nodeC : Spec.FramedCodec (Nat × Nat × Spec.Bytes × Spec.Bytes)
  leafC : Spec.FramedCodec (Nat × Nat × PackedFiber)
  contextC : Spec.FramedCodec WhirFsContext
  roundC : Spec.FramedCodec (List PackedRound)
  slotTreeDepth : Nat → Nat

/-- Reserve disjoint byte prefixes for the context (0), FS rounds (1),
    packed Merkle nodes (2) and packed Merkle leaves (3). -/
private def taggedWhirFrame {α : Type} (tag : UInt8) (c : Spec.FramedCodec α) : Spec.FramedCodec α where
  encode := fun x => tag :: c.encode x
  decodePrefix := fun bytes => match bytes with
    | [] => none
    | b :: rest => if b = tag then c.decodePrefix rest else none
  decodePrefix_append := fun x rest => by simp [c.decodePrefix_append]

def packedMerkleSetup (fr : SuccinctWhirByteFraming) (H : Spec.Bytes → Spec.Bytes) :
    MerkleSetup Spec.Bytes PackedFiber :=
  framedSetup H (taggedWhirFrame 2 fr.nodeC) (taggedWhirFrame 3 fr.leafC)

def whirContext {nVal : Nat} (logCells : Nat) (profile : AggSigProfile)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (proof : SuccinctWhirAggregateProof) :
    WhirFsContext :=
  ⟨logCells, profile, (List.finRange nVal).map stmt.roster, stmt.bitmap.toNat, stmt.message,
    proof.salt, proof.slotCommitRoot, proof.whirRoot0, proof.claim⟩

def whirRoundPreimage (fr : SuccinctWhirByteFraming) (ctx : WhirFsContext) (prefixRounds : List PackedRound) :
    Spec.Bytes := 1 :: (fr.contextC.encode ctx ++ fr.roundC.encode prefixRounds)

theorem whirRoundPreimage_injective (fr : SuccinctWhirByteFraming)
    {a b : WhirFsContext} {xs ys : List PackedRound}
    (h : whirRoundPreimage fr a xs = whirRoundPreimage fr b ys) : a = b ∧ xs = ys := by
  obtain ⟨hc, hr⟩ := fr.contextC.prefix_injective.mp (List.cons.inj h).2
  exact ⟨hc, fr.roundC.encode_injective hr⟩

/-- A changed message changes the address of every round, including when the prover
    supplies a different proof or edits earlier round messages. -/
theorem changed_message_round_addresses {nVal : Nat} (logCells : Nat) (profile : AggSigProfile)
    (fr : SuccinctWhirByteFraming) (stmt : Spec.AggregateStatement AggValidatorPk nVal) (msg : Spec.Bytes)
    (hne : stmt.message ≠ msg) (p p' : SuccinctWhirAggregateProof) (pre pre' : List PackedRound) :
    whirRoundPreimage fr (whirContext logCells profile stmt p) pre ≠
      whirRoundPreimage fr (whirContext logCells profile {stmt with message := msg} p') pre' := fun eq =>
  hne (congrArg WhirFsContext.message (whirRoundPreimage_injective fr eq).1)

/-- Read one fixed-width XOF squeeze at the framed prefix address. -/
def whirPrefixChallenge (fr : SuccinctWhirByteFraming) (H : Spec.Bytes → Spec.Bytes)
    (ctx : WhirFsContext) (prefixRounds : List PackedRound) : Option (BitVec packedChallengeBits) :=
  let bytes := H (whirRoundPreimage fr ctx prefixRounds)
  if bytes.length = packedChallengeBits / 8 then
    some (BitVec.ofNat _ (decodeNatLeBytes bytes))
  else none

private def deriveFsAux (fr : SuccinctWhirByteFraming) (H : Spec.Bytes → Spec.Bytes)
    (ctx : WhirFsContext) : List PackedRound → List PackedRound → Option (List (PackedRound × Nat))
  | _, [] => some []
  | pre, m :: rest => do
    let prefixRounds := pre ++ [m]
    let c ← whirPrefixChallenge fr H ctx prefixRounds
    let tail ← deriveFsAux fr H ctx prefixRounds rest
    return (m, c.toNat) :: tail

def deriveSuccinctFsTranscript (fr : SuccinctWhirByteFraming) (H : Spec.Bytes → Spec.Bytes)
    (ctx : WhirFsContext) (rounds : List PackedRound) : Option (List (PackedRound × Nat)) :=
  deriveFsAux fr H ctx [] rounds

/-- Pull the byte oracle back to the finite addresses of valid succinct prefixes.
    Malformed squeezes cannot occur on an accepted byte transcript. -/
def finiteWhirOracle {k n : Nat} (fr : SuccinctWhirByteFraming) (H : Spec.Bytes → Spec.Bytes)
    (ctx : WhirFsContext) (codec : FsCodec PackedRound k n) (o : Fin n) : BitVec packedChallengeBits :=
  (whirPrefixChallenge fr H ctx (codec.dec o)).getD 0

private theorem deriveFsAux_eq {k n : Nat} (fr : SuccinctWhirByteFraming) (H : Spec.Bytes → Spec.Bytes)
    (ctx : WhirFsContext) (codec : FsCodec PackedRound k n) (rest pre : List PackedRound)
    (tr : List (PackedRound × Nat)) (hlen : (pre ++ rest).length ≤ k)
    (hv : ∀ m ∈ pre ++ rest, codec.valid m = true) (h : deriveFsAux fr H ctx pre rest = some tr) :
    tr = fsAux codec (finiteWhirOracle fr H ctx codec) pre rest := by
  induction rest generalizing pre tr with
  | nil => simpa [deriveFsAux, fsAux.public_eq_1] using h.symm
  | cons m tail ih =>
    let next := pre ++ [m]
    have heq : next ++ tail = pre ++ m :: tail := by simp [next]
    have hlen' : next.length ≤ k := by simp only [List.length_append, List.length_cons] at hlen; simp [next]; omega
    have hv' : ∀ x ∈ next, codec.valid x = true := fun x hx =>
      hv x (heq ▸ List.mem_append_left tail hx)
    cases hc : whirPrefixChallenge fr H ctx next with
    | none => simp [deriveFsAux, ← show pre ++ [m] = next from rfl, hc, next] at h
    | some ch =>
      cases ht : deriveFsAux fr H ctx next tail with
      | none =>
        change (whirPrefixChallenge fr H ctx next >>= fun c =>
          deriveFsAux fr H ctx next tail >>= fun t => some ((m,c.toNat) :: t)) = some tr at h
        simp [hc, ht] at h
      | some t =>
        change (whirPrefixChallenge fr H ctx next >>= fun c =>
          deriveFsAux fr H ctx next tail >>= fun u => some ((m,c.toNat) :: u)) = some tr at h
        simp [hc, ht] at h
        rw [← h, fsAux.public_eq_2, ih next t (heq ▸ hlen) (heq ▸ hv) ht]
        simp only [finiteWhirOracle, codec.dec_enc _ hlen' hv', hc, Option.getD_some, next]

/-- Realize the finite FS oracle on the round addresses of one fixed statement
    context. The other domains delegate to the byte commitment oracle. -/
def realizeWhirFs {k n : Nat} (fr : SuccinctWhirByteFraming) (base : Spec.Bytes → Spec.Bytes)
    (ctx : WhirFsContext) (codec : FsCodec PackedRound k n) (H : Fin n → BitVec packedChallengeBits)
    (bytes : Spec.Bytes) : Spec.Bytes :=
  match bytes with
  | [] => base bytes
  | tag :: payload => if tag = 1 then
      let response := do
        let (c, rest) ← fr.contextC.decodePrefix payload
        guard (fr.contextC.encode c = fr.contextC.encode ctx)
        let (ms, tail) ← fr.roundC.decodePrefix rest
        guard tail.isEmpty
        return encodeNatLeBytes (packedChallengeBits / 8) (H (codec.enc ms)).toNat
      response.getD (base bytes)
    else base bytes

private theorem realized_challenge {k n : Nat} (fr : SuccinctWhirByteFraming) (base : Spec.Bytes → Spec.Bytes)
    (ctx : WhirFsContext) (codec : FsCodec PackedRound k n) (H : Fin n → BitVec packedChallengeBits)
    (ms : List PackedRound) :
    whirPrefixChallenge fr (realizeWhirFs fr base ctx codec H) ctx ms = some (H (codec.enc ms)) := by
  have hr := fr.roundC.decodePrefix_append ms []
  rw [List.append_nil] at hr
  have hb : (H (codec.enc ms)).toNat < 256^(packedChallengeBits/8) := by
    exact (H (codec.enc ms)).isLt
  simp [whirPrefixChallenge, whirRoundPreimage, realizeWhirFs, fr.contextC.decodePrefix_append, hr, guard,
    encodeNatLeBytes_length, decodeNatLeBytes_encodeNatLeBytes _ _ hb]

private theorem realized_transcript {k n : Nat} (fr : SuccinctWhirByteFraming) (base : Spec.Bytes → Spec.Bytes)
    (ctx : WhirFsContext) (codec : FsCodec PackedRound k n) (H : Fin n → BitVec packedChallengeBits)
    (rest pre : List PackedRound) :
    deriveFsAux fr (realizeWhirFs fr base ctx codec H) ctx pre rest = some (fsAux codec H pre rest) := by
  induction rest generalizing pre with
  | nil => rw [deriveFsAux, fsAux.public_eq_1]
  | cons m tail ih =>
    rw [deriveFsAux,fsAux.public_eq_2]; simp [realized_challenge,ih]

private theorem realized_merkle {k n : Nat} (fr : SuccinctWhirByteFraming) (base : Spec.Bytes → Spec.Bytes)
    (ctx : WhirFsContext) (codec : FsCodec PackedRound k n) (H : Fin n → BitVec packedChallengeBits) :
    packedMerkleSetup fr (realizeWhirFs fr base ctx codec H) = packedMerkleSetup fr base := by
  simp only [packedMerkleSetup,framedSetup.public_eq_1]; rfl

/-- All roots used by later stages must be present in their commit messages. -/
def packedRootsPresent (stages : List WhirStage) (rounds : List PackedRound) : Bool :=
  rounds.zipIdx.all fun (sm,r) =>
    match stageOfCommitRound stages r with
    | some j => sm.root.isSome == (j + 1 < stages.length)
    | none => sm.root.isNone

private def packedEnvelopeOk {nVal : Nat} (logCells : Nat)
    (profile : AggSigProfile) (fr : SuccinctWhirByteFraming) (H : Spec.Bytes → Spec.Bytes)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (proof : SuccinctWhirAggregateProof) : Bool :=
  let ctx := whirContext logCells profile stmt proof
  decide (16 ≤ logCells ∧ logCells ≤ 28 ∧ 0 < nVal) &&
  (List.finRange nVal).all (fun i => !stmt.bitmap.getLsbD i.val || (stmt.roster i).profile == profile) &&
  decide (proof.slotCommitRoot ≠ [] ∧ proof.whirRoot0 ≠ []) &&
  decide (proof.claim = QuinticGoldilocks.one) &&
  decide (proof.contextDigest = H (0 :: fr.contextC.encode ctx)) &&
  decide (proof.rounds.length = (packedProdSched logCells).numRounds) &&
  packedRootsPresent (packedProdStages logCells) proof.rounds

def verifySuccinctWhirAggregate {nVal : Nat} (logCells : Nat)
    (profile : AggSigProfile) (fr : SuccinctWhirByteFraming) (H : Spec.Bytes → Spec.Bytes)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (proof : SuccinctWhirAggregateProof) : Bool :=
  let ctx := whirContext logCells profile stmt proof
  packedEnvelopeOk logCells profile fr H stmt proof &&
  (deriveSuccinctFsTranscript fr H ctx proof.rounds).any (fun tr =>
    succinctVerify (packedWhirIop logCells) (packedBridge logCells)
      (packedMerkleSetup fr H) proof.claim (fun _ => proof.whirRoot0) tr proof.canopyOpenings)

/-- An accepted byte proof gives acceptance of the same packed proof in the finite FS
    experiment at its decoded output. Both use the same Merkle functions and openings. -/
theorem verifySuccinctWhirAggregate_finite_accept {nVal logCells n : Nat} {profile : AggSigProfile}
    {fr : SuccinctWhirByteFraming} {H : Spec.Bytes → Spec.Bytes}
    {stmt : Spec.AggregateStatement AggValidatorPk nVal} {p : SuccinctWhirAggregateProof}
    (ha : verifySuccinctWhirAggregate logCells profile fr H stmt p = true)
    (codec : FsCodec PackedRound (packedProdSched logCells).numRounds n) (o : Fin n)
    (ho : codec.dec o = p.rounds) (ops : Fin n → List (PackedFiber × List Spec.Bytes))
    (hop : ops o = p.canopyOpenings) :
    succinctFsAccept (packedWhirIop logCells) (packedBridge logCells) (packedMerkleSetup fr H)
      codec ops p.claim (fun _ => p.whirRoot0) (finiteWhirOracle fr H (whirContext logCells profile stmt p) codec) o = true := by
  simp only [verifySuccinctWhirAggregate, packedEnvelopeOk, Bool.and_eq_true, decide_eq_true_eq] at ha
  let ctx := whirContext logCells profile stmt p
  have hv := ha.2
  cases ht : deriveSuccinctFsTranscript fr H ctx p.rounds with
  | none => rw [ht] at hv; contradiction
  | some tr =>
    rw [ht] at hv
    have eq := deriveFsAux_eq fr H ctx codec p.rounds [] tr (Nat.le_of_eq ha.1.1.2)
      (fun m hm => codec.dec_valid o m (ho ▸ hm)) ht
    rw [succinctFsAccept.public_eq_1 (packedWhirIop logCells) (packedBridge logCells)
      (packedMerkleSetup fr H) codec ops p.claim (fun _ => p.whirRoot0)
      (finiteWhirOracle fr H ctx codec) o]
    change succinctVerify (packedWhirIop logCells) (packedBridge logCells) (packedMerkleSetup fr H)
      p.claim (fun _ => p.whirRoot0) (@fsTranscript PackedRound _ _ packedChallengeBits codec
        (finiteWhirOracle fr H ctx codec) (codec.dec o)) (ops o) = true
    rw [fsTranscript.public_eq_1 codec (finiteWhirOracle fr H ctx codec) (codec.dec o), ho, hop, ← eq]
    exact hv

/-- Rebuild an adversary output at the fixed statement, salt, initial roots and
    claim of the experiment. The context digest is public. -/
def packedProofAt {n : Nat} (template : SuccinctWhirAggregateProof) (digest : Spec.Bytes)
    (rounds : Fin n → List PackedRound) (ops : Fin n → List (PackedFiber × List Spec.Bytes))
    (o : Fin n) : SuccinctWhirAggregateProof :=
  {template with rounds := rounds o, canopyOpenings := ops o, contextDigest := digest}

def packedByteEvent {nVal n : Nat} (logCells : Nat) (profile : AggSigProfile) (fr : SuccinctWhirByteFraming)
    (base : Spec.Bytes → Spec.Bytes) (stmt : Spec.AggregateStatement AggValidatorPk nVal)
    (template : SuccinctWhirAggregateProof) (codec : FsCodec PackedRound (packedProdSched logCells).numRounds n)
    (ops : Fin n → List (PackedFiber × List Spec.Bytes)) (H : Fin n → BitVec packedChallengeBits) (o : Fin n) : Bool :=
  let ctx := whirContext logCells profile stmt template
  verifySuccinctWhirAggregate logCells profile fr (realizeWhirFs fr base ctx codec H) stmt
    (packedProofAt template (base (0 :: fr.contextC.encode ctx)) codec.dec ops o)

theorem packedByteEvent_accept {nVal n : Nat} (logCells : Nat) (profile : AggSigProfile)
    (fr : SuccinctWhirByteFraming) (base : Spec.Bytes → Spec.Bytes)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (template : SuccinctWhirAggregateProof)
    (codec : FsCodec PackedRound (packedProdSched logCells).numRounds n)
    (ops : Fin n → List (PackedFiber × List Spec.Bytes)) (H : Fin n → BitVec packedChallengeBits) (o : Fin n)
    (ha : packedByteEvent logCells profile fr base stmt template codec ops H o = true) :
    succinctFsAccept (packedWhirIop logCells) (packedBridge logCells) (packedMerkleSetup fr base) codec ops
      template.claim (fun _ => template.whirRoot0) H o = true := by
  let ctx := whirContext logCells profile stmt template
  simp only [packedByteEvent, verifySuccinctWhirAggregate, packedEnvelopeOk, Bool.and_eq_true] at ha
  have hv := ha.2
  change (deriveFsAux fr (realizeWhirFs fr base ctx codec H) ctx [] (codec.dec o)).any
    (fun tr => succinctVerify _ _ (packedMerkleSetup fr (realizeWhirFs fr base ctx codec H)) template.claim
      (fun _ => template.whirRoot0) tr (ops o)) = true at hv
  rw [realized_transcript,Option.any_some,realized_merkle] at hv
  rw [succinctFsAccept.public_eq_1 (packedWhirIop logCells) (packedBridge logCells) _ codec ops
    template.claim (fun _ => template.whirRoot0) H o]
  change succinctVerify _ _ _ _ _ (@fsTranscript PackedRound _ _ packedChallengeBits codec H (codec.dec o)) _ = true
  rw [fsTranscript.public_eq_1 codec H]; exact hv

theorem verifySuccinctWhirAggregate_context {nVal logCells : Nat} {profile : AggSigProfile}
    {fr : SuccinctWhirByteFraming} {H : Spec.Bytes → Spec.Bytes}
    {stmt : Spec.AggregateStatement AggValidatorPk nVal} {p : SuccinctWhirAggregateProof}
    (h : verifySuccinctWhirAggregate logCells profile fr H stmt p = true) :
    p.contextDigest = H (0 :: fr.contextC.encode (whirContext logCells profile stmt p)) := by
  simp only [verifySuccinctWhirAggregate, packedEnvelopeOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem changed_message_collision {nVal logCells : Nat} {profile : AggSigProfile}
    {fr : SuccinctWhirByteFraming} {H : Spec.Bytes → Spec.Bytes}
    {stmt : Spec.AggregateStatement AggValidatorPk nVal} {p : SuccinctWhirAggregateProof}
    (h : verifySuccinctWhirAggregate logCells profile fr H stmt p = true) (msg : Spec.Bytes)
    (hne : stmt.message ≠ msg)
    (h' : verifySuccinctWhirAggregate logCells profile fr H {stmt with message := msg} p = true) :
    Spec.ValidBreak H ⟨0 :: fr.contextC.encode (whirContext logCells profile stmt p),
      0 :: fr.contextC.encode (whirContext logCells profile {stmt with message := msg} p)⟩ := by
  apply (Spec.ValidBreak_iff _ _).mpr
  refine ⟨fun eq => hne (congrArg WhirFsContext.message
    (fr.contextC.encode_injective (List.cons.inj eq).2)), ?_⟩
  exact (verifySuccinctWhirAggregate_context h).symm.trans (verifySuccinctWhirAggregate_context h')

theorem tooth_changed_message_rejected {nVal logCells : Nat} {profile : AggSigProfile}
    {fr : SuccinctWhirByteFraming} {H : Spec.Bytes → Spec.Bytes}
    {stmt : Spec.AggregateStatement AggValidatorPk nVal} {p : SuccinctWhirAggregateProof}
    (h : verifySuccinctWhirAggregate logCells profile fr H stmt p = true) (msg : Spec.Bytes)
    (hne : stmt.message ≠ msg)
    (hBound : ¬ Spec.ValidBreak H ⟨0 :: fr.contextC.encode (whirContext logCells profile stmt p),
      0 :: fr.contextC.encode (whirContext logCells profile {stmt with message := msg} p)⟩) :
    verifySuccinctWhirAggregate logCells profile fr H {stmt with message := msg} p = false := by
  cases h' : verifySuccinctWhirAggregate logCells profile fr H {stmt with message := msg} p
  · rfl
  · exact absurd (changed_message_collision h msg hne h') hBound

/-! ## §4. Straight-Line QROM Query-Table Extractor, `< 2^{-128}` Soundness & `Spec.IdealAggregate` Refinement -/

/-- Parse recorded Merkle node queries `(lvl, node, left, right) ↦ out` from the byte oracle `log`. -/
def parseRecordedMerkleNodes (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (log : List (Spec.Bytes × Spec.Bytes)) : List (RecordedMerkleQuery Spec.Bytes) :=
  log.filterMap fun e =>
    match nodeDecode e.1 with
    | some (lvl, node, l, r) => some ⟨lvl, node, l, r, e.2⟩
    | none => none

/-- Walk from the committed root, then locate the first matching salted leaf preimage. -/
def recordedSlotRows {nVal : Nat} (profile : AggSigProfile) (fr : SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (slotC : SlotLeafTableCodec) (log : List (Spec.Bytes × Spec.Bytes))
    (proof : SuccinctWhirAggregateProof) (i : Fin nVal) : Option (List StepOpRow) := do
  let (digest, _) ← extractOnlineMerkleOpening proof.slotCommitRoot
    (parseRecordedMerkleNodes nodeDecode log) 0 (fr.slotTreeDepth nVal) i.val
  log.findSome? fun e => do
    let (salt, prof, idx, rows) ← slotC.decode e.1
    if e.2 = digest ∧ salt = proof.salt ∧ prof = profile ∧ idx = i.val then some rows else none

/-- Missing openings have the empty row table in the measured AIR game. -/
def reconstructedSlotRows {nVal : Nat} (profile : AggSigProfile) (fr : SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (slotC : SlotLeafTableCodec) (log : List (Spec.Bytes × Spec.Bytes))
    (proof : SuccinctWhirAggregateProof) (i : Fin nVal) : List StepOpRow :=
  (recordedSlotRows profile fr nodeDecode slotC log proof i).getD []

/-- Extract the native signature from the recorded table of the specified slot. -/
def extractSuccinctWhirAggregate {nVal : Nat} (profile : AggSigProfile) (fr : SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (slotC : SlotLeafTableCodec) (log : List (Spec.Bytes × Spec.Bytes))
    (_stmt : Spec.AggregateStatement AggValidatorPk nVal) (proof : SuccinctWhirAggregateProof)
    (i : Fin nVal) : Option AggNativeSignature :=
  (recordedSlotRows profile fr nodeDecode slotC log proof i).map (fun rows => extractSlotNativeSig profile rows 0)

theorem extractSuccinctWhirAggregate_straightLine {nVal : Nat}
    (profile : AggSigProfile) (fr : SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (slotC : SlotLeafTableCodec) :
    Spec.StraightLineExtractor (PK := AggValidatorPk)
      (decodeSlotLeafSig slotC) succinctWhirProofSigs
      (extractSuccinctWhirAggregate (nVal := nVal) profile fr nodeDecode slotC) := by
  rw [Spec.StraightLineExtractor_iff]
  intro log stmt proof i sig hExt
  obtain ⟨rows, hr, rfl⟩ := Option.map_eq_some_iff.mp hExt
  unfold recordedSlotRows at hr
  obtain ⟨⟨digest, path⟩, _, hf⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨e, he, hs⟩ := List.exists_of_findSome?_eq_some hf
  dsimp only at hs
  obtain ⟨⟨salt, prof, idx, rs⟩, hd, hrows⟩ := Option.bind_eq_some_iff.mp hs
  dsimp only at hrows
  split at hrows
  · rename_i hm
    obtain ⟨_, _, rfl, _⟩ := hm
    exact .inr ⟨e, he, .inl (by simp [decodeSlotLeafSig, hd, Option.some.inj hrows])⟩
  · contradiction

/-- Closed QROM reduction for the same packed IOP and bridge used by the byte verifier.
    The algebraic certificate and the Merkle collision estimate are separate obligations. -/
theorem packedWhir_qrom_soundness_128
    (logCells : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28)
    (prof : WhirCommitmentProfile) {cardX cardAnc Q : Nat} (hQ : Q ≤ 2 ^ 64)
    (M : MerkleSetup Spec.Bytes PackedFiber)
    (cert : BoolRbrCert (packedWhirIop logCells))
    (covers : ∀ r, RatBound.le
      ⟨cert.bad r, 2 ^ packedChallengeBits, Nat.two_pow_pos _⟩
      ((packedStagesRoundBounds quinticGoldilocksCard quinticGoldilocksCard_pos
        (packedProdStages logCells)).getD r.val RatBound.one))
    (codec : FsCodec PackedRound (packedProdSched logCells).numRounds cardX)
    (aux : Fin cardX → List (PackedFiber × List Spec.Bytes)) (claim : QuinticGoldilocks)
    (initRoots : Nat → Spec.Bytes) (tbl : Nat → Spec.Bytes → Nat → PackedFiber)
    (hx : ¬ (packedWhirIop logCells).inLang ((packedBridge logCells).liftStmt claim initRoots tbl))
    (hRoots : ∀ H o, succinctFsAccept (packedWhirIop logCells) (packedBridge logCells)
        M codec aux claim initRoots H o = true →
      let str := fsTranscript codec H (codec.dec o)
      ∀ q ∈ (packedWhirIop logCells).queries claim (str.map fun sc => (sc.1.pub, sc.2)),
        let root := (packedBridge logCells).rootsOf initRoots (str.map Prod.fst) q.1
        M.root q.1 ((packedWhirIop logCells).depth q.1) (tbl q.1 root) = root)
    (A : QuantumAdv cardX packedChallengeBits cardAnc Q)
    (hMerkle : RatBound.le
      ⟨uniformOracleSum packedChallengeBits cardX (fun H =>
        QVec.queryMassOn (succinctFsCollisionEvent (packedWhirIop logCells) (packedBridge logCells)
          M codec aux claim initRoots tbl H) (runQuantumAdv A H)),
        (2 ^ packedChallengeBits) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _)) (Nat.mul_pos (prefixScale_pos A Q _) A.h_init_pos)⟩
      (merkleProfileQromBound prof Q)) :
    RatBound.lt
      ⟨uniformOracleSum packedChallengeBits cardX (fun H =>
        QVec.queryMassOn (succinctFsAccept (packedWhirIop logCells) (packedBridge logCells)
          M codec aux claim initRoots H) (runQuantumAdv A H)),
        (2 ^ packedChallengeBits) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _)) (Nat.mul_pos (prefixScale_pos A Q _) A.h_init_pos)⟩
      (RatBound.invPow2 128) := by
  have hClosed := succinct_fs_qrom_closed_soundness (packedWhirIop logCells) (packedBridge logCells)
    M cert codec aux claim initRoots tbl hx hRoots A
  have hSum := dfm_sum_le Q packedChallengeBits _ cert.bad _
    (packedStagesRoundBounds_length _ _ (packedProdStages logCells)) covers
  rw [← packedProdQromError_eq] at hSum
  exact ratBound_lt_of_le_of_lt_packed (RatBound.le_trans hClosed (RatBound.add_le_add hSum hMerkle))
    (zkHemV2_packed_all13_budget_lt_128 prof logCells Q hLo hHi hQ)

/-- QROM acceptance bound for the byte verifier evaluated on the fixed context's
    finite random-oracle experiment. Its commitments and claimed opening are
    fixed before sampling the FS oracle. The bound requires the corresponding
    packed algebraic certificate, reconstructed Merkle roots and collision estimate. -/
theorem succinctWhirAggregate_qrom_soundness_128
    {nVal : Nat} (logCells : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28)
    (prof : WhirCommitmentProfile) {cardX cardAnc Q : Nat} (hQ : Q ≤ 2 ^ 64)
    (profile : AggSigProfile) (fr : SuccinctWhirByteFraming) (base : Spec.Bytes → Spec.Bytes)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (template : SuccinctWhirAggregateProof)
    (cert : BoolRbrCert (packedWhirIop logCells))
    (covers : ∀ r, RatBound.le
      ⟨cert.bad r, 2 ^ packedChallengeBits, Nat.two_pow_pos _⟩
      ((packedStagesRoundBounds quinticGoldilocksCard quinticGoldilocksCard_pos
        (packedProdStages logCells)).getD r.val RatBound.one))
    (codec : FsCodec PackedRound (packedProdSched logCells).numRounds cardX)
    (aux : Fin cardX → List (PackedFiber × List Spec.Bytes))
    (tbl : Nat → Spec.Bytes → Nat → PackedFiber)
    (hx : ¬ (packedWhirIop logCells).inLang ((packedBridge logCells).liftStmt template.claim (fun _ => template.whirRoot0) tbl))
    (hRoots : ∀ H o, succinctFsAccept (packedWhirIop logCells) (packedBridge logCells)
        (packedMerkleSetup fr base) codec aux template.claim (fun _ => template.whirRoot0) H o = true →
      let str := fsTranscript codec H (codec.dec o)
      ∀ q ∈ (packedWhirIop logCells).queries template.claim (str.map fun sc => (sc.1.pub, sc.2)),
        let root := (packedBridge logCells).rootsOf (fun _ => template.whirRoot0) (str.map Prod.fst) q.1
        (packedMerkleSetup fr base).root q.1 ((packedWhirIop logCells).depth q.1) (tbl q.1 root) = root)
    (A : QuantumAdv cardX packedChallengeBits cardAnc Q)
    (hMerkle : RatBound.le
      ⟨uniformOracleSum packedChallengeBits cardX (fun H =>
        QVec.queryMassOn (succinctFsCollisionEvent (packedWhirIop logCells) (packedBridge logCells)
          (packedMerkleSetup fr base) codec aux template.claim (fun _ => template.whirRoot0) tbl H) (runQuantumAdv A H)),
        (2 ^ packedChallengeBits) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _)) (Nat.mul_pos (prefixScale_pos A Q _) A.h_init_pos)⟩
      (merkleProfileQromBound prof Q)) :
    RatBound.lt
      ⟨uniformOracleSum packedChallengeBits cardX (fun H =>
        QVec.queryMassOn (packedByteEvent logCells profile fr base stmt template codec aux H) (runQuantumAdv A H)),
        (2 ^ packedChallengeBits) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _)) (Nat.mul_pos (prefixScale_pos A Q _) A.h_init_pos)⟩
      (RatBound.invPow2 128) := by
  have hFinite := packedWhir_qrom_soundness_128 logCells hLo hHi prof hQ (packedMerkleSetup fr base)
    cert covers codec aux template.claim (fun _ => template.whirRoot0) tbl hx hRoots A hMerkle
  apply ratBound_lt_of_le_of_lt_packed _ hFinite
  apply Nat.mul_le_mul_right
  apply uniformOracleSum_le
  intro H
  apply QVec.queryMassOn_mono
  exact fun o => packedByteEvent_accept logCells profile fr base stmt template codec aux H o

/-- The three-stage schedule supplies its algebraic certificate and round coverage. -/
theorem zkHemV2MultiStage_qrom_soundness_128 : type_of% @zkHemV2MultiStage_succinct_qrom_128 := @zkHemV2MultiStage_succinct_qrom_128

/-- Convert a QROM `RatBound` (`h_pos`) to `Spec.RatBound` (`den_pos`) preserving `< 2^{-128}`. -/
@[expose] def toSpecRatBound (b : RatBound) : Spec.RatBound :=
  ⟨b.num, b.den, b.h_pos⟩

/-- The row relation needed from the WHIR arithmetization on an active slot. -/
def slotTablesValid {nVal : Nat} (profile : AggSigProfile)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (rows : Fin nVal → List StepOpRow) : Bool :=
  (List.finRange nVal).all fun i => !stmt.bitmap.getLsbD i.val ||
    stepOp256TableOk profile [some (stmt.roster i, computeMessageMu (stmt.roster i) stmt.message)] (rows i)

/-- Agreement of the log extractor with the signature carried by each reconstructed active slot. -/
def slotSignaturesRecovered {nVal : Nat} (profile : AggSigProfile)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (rows : Fin nVal → List StepOpRow)
    (sigs : Fin nVal → Option AggNativeSignature) : Bool :=
  (List.finRange nVal).all fun i => !stmt.bitmap.getLsbD i.val ||
    decide (sigs i = some (extractSlotNativeSig profile (rows i) 0))

/-- Two byte-game obligations on the same backing rows for each prover and coin split.
    The first bounds failed AIR checks and the second bounds failed log recovery. -/
def PackedSlotGameBounds {nVal nC : Nat} (logCells : Nat) (profile : AggSigProfile)
    (prof : WhirCommitmentProfile) (fr : SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes)) (slotC : SlotLeafTableCodec)
    (oracle : Fin nC → Spec.Bytes → Spec.Bytes) (Q : Nat) : Prop :=
  ∀ (n nA : Nat) (hPos : 0 < n) (π : Spec.CoinSplit n nC nA)
    (prover : Fin nA → Spec.Code Spec.byteOracleIface
      (Spec.AggregateStatement AggValidatorPk nVal × SuccinctWhirAggregateProof)),
    let H := fun ω => oracle (π.chal ω)
    let run := fun ω => Spec.aggregateRun (H ω) Q (prover (π.advc ω))
    let acc := fun ω => verifySuccinctWhirAggregate logCells profile fr (H ω) (run ω).1.1 (run ω).1.2
    ∃ rows : Fin n → Fin nVal → List StepOpRow,
      Spec.GameBound (Spec.FinGame.mk hPos (fun ω => acc ω &&
        !slotTablesValid profile (run ω).1.1 (rows ω))).winProb
        (toSpecRatBound (packedProdQromError logCells Q)) ∧
      Spec.GameBound (Spec.FinGame.mk hPos (fun ω => acc ω &&
        !slotSignaturesRecovered profile (run ω).1.1 (rows ω)
          (extractSuccinctWhirAggregate profile fr nodeDecode slotC
            (run ω).2 (run ω).1.1 (run ω).1.2))).winProb
        (toSpecRatBound (merkleProfileQromBound prof Q))

private theorem validExtractedSlots {nVal logCells : Nat} {profile : AggSigProfile}
    {fr : SuccinctWhirByteFraming} {H : Spec.Bytes → Spec.Bytes}
    {stmt : Spec.AggregateStatement AggValidatorPk nVal} {p : SuccinctWhirAggregateProof}
    (ha : verifySuccinctWhirAggregate logCells profile fr H stmt p = true)
    (rows : Fin nVal → List StepOpRow) (sigs : Fin nVal → Option AggNativeSignature)
    (ht : slotTablesValid profile stmt rows = true) (he : slotSignaturesRecovered profile stmt rows sigs = true) :
    Spec.ValidAggregateWitness (verifyAggNativeSig (profileGeom profile)) stmt sigs := by
  simp only [verifySuccinctWhirAggregate, packedEnvelopeOk, Bool.and_eq_true] at ha
  have hp := ha.1.1.1.1.1.1.2
  apply Spec.ValidAggregateWitness.intro
  intro i hi
  have hProf := List.all_eq_true.mp hp i (List.mem_finRange i)
  have hTable := List.all_eq_true.mp ht i (List.mem_finRange i)
  have hExt := List.all_eq_true.mp he i (List.mem_finRange i)
  simp only [hi, Bool.not_true, Bool.false_or, beq_iff_eq, decide_eq_true_eq] at hProf hTable hExt
  have hd : IsDeployedAggProfile profile := by cases profile <;> simp [IsDeployedAggProfile]
  exact ⟨_, hExt, singleSlot_stepOp256_extract profile hd _ _ _ hProf hTable⟩

/-- Every active slot has a matching salted preimage along its recorded Merkle path. -/
def slotOpeningsRecorded {nVal : Nat} (stmt : Spec.AggregateStatement AggValidatorPk nVal)
    (openings : Fin nVal → Option (List StepOpRow)) : Bool :=
  (List.finRange nVal).all fun i => !stmt.bitmap.getLsbD i.val || (openings i).isSome

section Measured
variable {nVal : Nat} (logCells : Nat) (profile : AggSigProfile) (fr : SuccinctWhirByteFraming)
  (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes)) (slotC : SlotLeafTableCodec)

theorem slotSignaturesRecovered_reconstructed (log : List (Spec.Bytes × Spec.Bytes))
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (p : SuccinctWhirAggregateProof) :
    slotSignaturesRecovered profile stmt (reconstructedSlotRows profile fr nodeDecode slotC log p)
      (extractSuccinctWhirAggregate profile fr nodeDecode slotC log stmt p) =
    slotOpeningsRecorded stmt (recordedSlotRows profile fr nodeDecode slotC log p) := by
  unfold slotSignaturesRecovered slotOpeningsRecorded
  congr 1
  funext i
  cases ho : recordedSlotRows profile fr nodeDecode slotC log p i <;>
    simp [extractSuccinctWhirAggregate, reconstructedSlotRows, ho]

variable {n : Nat} (hPos : 0 < n) (H : Fin n → Spec.Bytes → Spec.Bytes) (Q : Nat)
  (prover : Fin n → Spec.Code Spec.byteOracleIface
    (Spec.AggregateStatement AggValidatorPk nVal × SuccinctWhirAggregateProof))

/-- Two events on the same coins and recording-oracle run: acceptance with an invalid
    reconstructed AIR table, and acceptance with a missing active slot opening. -/
def measuredSlotGames : Spec.FinGame n × Spec.FinGame n :=
  let run := fun ω => Spec.aggregateRun (H ω) Q (prover ω)
  let acc := fun ω => verifySuccinctWhirAggregate logCells profile fr (H ω) (run ω).1.1 (run ω).1.2
  (⟨hPos, fun ω => acc ω && !slotTablesValid profile (run ω).1.1
    (reconstructedSlotRows profile fr nodeDecode slotC (run ω).2 (run ω).1.2)⟩,
   ⟨hPos, fun ω => acc ω && !slotOpeningsRecorded (run ω).1.1
    (recordedSlotRows profile fr nodeDecode slotC (run ω).2 (run ω).1.2)⟩)

/-- Finite-game extraction failure is bounded by the two measured error probabilities. -/
theorem measuredSuccinctWhirAggregate_extractorSound :
    let games := measuredSlotGames logCells profile fr nodeDecode slotC hPos H Q prover
    Spec.GameBound (Spec.aggregateSoundnessGame hPos (verifyAggNativeSig (profileGeom profile))
      (verifySuccinctWhirAggregate logCells profile fr)
      (extractSuccinctWhirAggregate profile fr nodeDecode slotC) Q H prover).winProb
      (Spec.RatBound.add games.1.winProb games.2.winProb) := by
  apply Spec.event_le_two_reductions
  intro ω hw
  obtain ⟨ha, hn⟩ := Spec.aggregateSoundnessGame_win_invalid _ _ _ _ _ _ _ ω hw
  let r := Spec.aggregateRun (H ω) Q (prover ω)
  let rows := reconstructedSlotRows (nVal := nVal) profile fr nodeDecode slotC r.2 r.1.2
  let openings := recordedSlotRows (nVal := nVal) profile fr nodeDecode slotC r.2 r.1.2
  change (_ && !slotTablesValid profile r.1.1 rows) = true ∨ (_ && !slotOpeningsRecorded r.1.1 openings) = true
  dsimp only
  rw [ha, Bool.true_and, Bool.true_and]
  cases ht : slotTablesValid profile r.1.1 rows with
  | false => exact .inl rfl
  | true =>
    cases ho : slotOpeningsRecorded r.1.1 openings with
    | false => exact .inr rfl
    | true =>
      rw [← slotSignaturesRecovered_reconstructed profile fr nodeDecode slotC r.2 r.1.1 r.1.2] at ho
      exact absurd (validExtractedSlots ha rows _ ht ho) hn

/-- Install measured bounds for every split with the canonical reconstructed tables. -/
theorem packedSlotGameBounds_of_reconstructed {nC : Nat} (prof : WhirCommitmentProfile)
    (oracle : Fin nC → Spec.Bytes → Spec.Bytes) (Q : Nat)
    (bounds : ∀ (n nA : Nat) (hPos : 0 < n) (π : Spec.CoinSplit n nC nA)
      (prover : Fin nA → Spec.Code Spec.byteOracleIface
        (Spec.AggregateStatement AggValidatorPk nVal × SuccinctWhirAggregateProof)),
      let games := measuredSlotGames logCells profile fr nodeDecode slotC hPos
        (fun ω => oracle (π.chal ω)) Q (fun ω => prover (π.advc ω))
      Spec.GameBound games.1.winProb (toSpecRatBound (packedProdQromError logCells Q)) ∧
      Spec.GameBound games.2.winProb (toSpecRatBound (merkleProfileQromBound prof Q))) :
    PackedSlotGameBounds (nVal := nVal) logCells profile prof fr nodeDecode slotC oracle Q := by
  intro n nA hPos π prover
  let run := fun ω => Spec.aggregateRun (oracle (π.chal ω)) Q (prover (π.advc ω))
  refine ⟨fun ω => reconstructedSlotRows profile fr nodeDecode slotC (run ω).2 (run ω).1.2,
    (bounds n nA hPos π prover).1, ?_⟩
  simpa only [run, measuredSlotGames, slotSignaturesRecovered_reconstructed] using (bounds n nA hPos π prover).2

end Measured

/-- The byte-game bounds on active slot tables and query-log recovery imply aggregate extraction soundness for both native signature profiles. -/
theorem succinctWhirAggregate_extractorSound {nVal nC : Nat}
    (logCells : Nat) (profile : AggSigProfile) (prof : WhirCommitmentProfile) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28)
    (fr : SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (slotC : SlotLeafTableCodec)
    (oracle : Fin nC → Spec.Bytes → Spec.Bytes) (Q : Nat) (hQ : Q ≤ 2 ^ 64)
    (hSlots : PackedSlotGameBounds (nVal := nVal) logCells profile prof fr nodeDecode slotC oracle Q) :
    let ε := toSpecRatBound
      (RatBound.add (packedProdQromError logCells Q) (merkleProfileQromBound prof Q))
    Spec.AggregateExtractorSound
      (Spec.StraightLineExtractor (decodeSlotLeafSig slotC) succinctWhirProofSigs)
      (verifyAggNativeSig (profileGeom profile))
      (verifySuccinctWhirAggregate (nVal := nVal) logCells profile fr)
      (extractSuccinctWhirAggregate (nVal := nVal) profile fr nodeDecode slotC)
      oracle Q ε ∧
    ε.num * 2 ^ 128 < 1 * ε.den := by
  intro ε
  refine ⟨⟨extractSuccinctWhirAggregate_straightLine profile fr nodeDecode slotC, ?_⟩,
    zkHemV2_packed_all13_budget_lt_128 prof logCells Q hLo hHi hQ⟩
  intro n nA hPos π prover
  obtain ⟨rows, ht, he⟩ := hSlots n nA hPos π prover
  apply Spec.GameBound.trans (Spec.event_le_two_reductions _ _ _ ?_) (Spec.RatBound.add_le_add ht he)
  intro ω hw
  obtain ⟨ha, hn⟩ := Spec.aggregateSoundnessGame_win_invalid _ _ _ _ _ _ _ ω hw
  let r := Spec.aggregateRun (oracle (π.chal ω)) Q (prover (π.advc ω))
  let sigs := extractSuccinctWhirAggregate profile fr nodeDecode slotC r.2 r.1.1 r.1.2
  dsimp only
  rw [ha, Bool.true_and, Bool.true_and]
  cases ht' : slotTablesValid profile r.1.1 (rows ω) with
  | false => exact .inl rfl
  | true =>
    cases he' : slotSignaturesRecovered profile r.1.1 (rows ω) sigs with
    | false => exact .inr rfl
    | true => exact absurd (validExtractedSlots ha (rows ω) sigs ht' he') hn

/-- The measured probability that the public machine accepts and the ideal
    machine rejects the extracted signatures. -/
theorem measuredSuccinctWhirAggregate_refines_idealAggregate {nVal n : Nat}
    (logCells : Nat) (profile : AggSigProfile) (fr : SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes)) (slotC : SlotLeafTableCodec)
    (hPos : 0 < n) (H : Fin n → Spec.Bytes → Spec.Bytes) (Q : Nat)
    (prover : Fin n → Spec.Code Spec.byteOracleIface
      (Spec.AggregateStatement AggValidatorPk nVal × SuccinctWhirAggregateProof)) :
    let extract := extractSuccinctWhirAggregate (nVal := nVal) profile fr nodeDecode slotC
    let single := verifyAggNativeSig (profileGeom profile)
    let verify := verifySuccinctWhirAggregate (nVal := nVal) logCells profile fr
    let games := measuredSlotGames logCells profile fr nodeDecode slotC hPos H Q prover
    Spec.GameBound (Spec.aggregateRefinementGame hPos single verify extract Q H prover).winProb
      (Spec.RatBound.add games.1.winProb games.2.winProb) := by
  intro extract single verify games
  apply Spec.event_le_two_reductions
  intro ω hw
  obtain ⟨ha, hn⟩ := (Spec.aggregateRefinementGame_win ..).mp hw
  dsimp only [verify] at ha
  let r := Spec.aggregateRun (H ω) Q (prover ω)
  let rows := reconstructedSlotRows (nVal := nVal) profile fr nodeDecode slotC r.2 r.1.2
  let openings := recordedSlotRows (nVal := nVal) profile fr nodeDecode slotC r.2 r.1.2
  change (_ && !slotTablesValid profile r.1.1 rows) = true ∨ (_ && !slotOpeningsRecorded r.1.1 openings) = true
  dsimp only
  rw [ha, Bool.true_and, Bool.true_and]
  cases ht : slotTablesValid profile r.1.1 rows with
  | false => exact .inl rfl
  | true =>
    cases ho : slotOpeningsRecorded r.1.1 openings with
    | false => exact .inr rfl
    | true =>
      rw [← slotSignaturesRecovered_reconstructed profile fr nodeDecode slotC r.2 r.1.1 r.1.2] at ho
      exact absurd (validExtractedSlots ha rows _ ht ho) hn

/-- The same public-to-ideal discrepancy under the packed slot bounds. -/
theorem succinctWhirAggregate_refines_idealAggregate_128 {nVal nC n nA : Nat}
    (logCells : Nat) (profile : AggSigProfile) (prof : WhirCommitmentProfile) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28)
    (fr : SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (slotC : SlotLeafTableCodec)
    (oracle : Fin nC → Spec.Bytes → Spec.Bytes) (Q : Nat) (hQ : Q ≤ 2 ^ 64)
    (hPos : 0 < n) (π : Spec.CoinSplit n nC nA)
    (prover : Fin nA → Spec.Code Spec.byteOracleIface
      (Spec.AggregateStatement AggValidatorPk nVal × SuccinctWhirAggregateProof))
    (hSlots : PackedSlotGameBounds (nVal := nVal) logCells profile prof fr nodeDecode slotC oracle Q) :
    let ε := toSpecRatBound
      (RatBound.add (packedProdQromError logCells Q) (merkleProfileQromBound prof Q))
    Spec.GameBound (Spec.aggregateRefinementGame hPos (verifyAggNativeSig (profileGeom profile))
      (verifySuccinctWhirAggregate logCells profile fr) (extractSuccinctWhirAggregate profile fr nodeDecode slotC)
      Q (fun ω => oracle (π.chal ω)) (fun ω => prover (π.advc ω))).winProb ε ∧
      ε.num * 2^128 < 1 * ε.den := by
  intro ε
  obtain ⟨rows, ht, he⟩ := hSlots n nA hPos π prover
  refine ⟨Spec.GameBound.trans (Spec.event_le_two_reductions _ _ _ ?_) (Spec.RatBound.add_le_add ht he), ?_⟩
  · intro ω hw
    obtain ⟨ha, hn⟩ := (Spec.aggregateRefinementGame_win ..).mp hw
    let r := Spec.aggregateRun (oracle (π.chal ω)) Q (prover (π.advc ω))
    let sigs := extractSuccinctWhirAggregate profile fr nodeDecode slotC r.2 r.1.1 r.1.2
    dsimp only
    rw [ha, Bool.true_and, Bool.true_and]
    cases ht' : slotTablesValid profile r.1.1 (rows ω) with
    | false => exact .inl rfl
    | true =>
      cases he' : slotSignaturesRecovered profile r.1.1 (rows ω) sigs with
      | false => exact .inr rfl
      | true => exact absurd (validExtractedSlots ha (rows ω) sigs ht' he') hn
  · exact zkHemV2_packed_all13_budget_lt_128 prof logCells Q hLo hHi hQ

/-- Under the packed slot game estimates, an accepted active signer gives participation, a transcript break or a quorum forgery outside the bounded failure event. -/
theorem succinctWhirAggregate_quorum_euf_cma_reduction {nVal nC n nA : Nat}
    (logCells : Nat) (profile : AggSigProfile) (prof : WhirCommitmentProfile) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28)
    (custody : Fin nVal → Composed.Custody)
    (fr : SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (slotC : SlotLeafTableCodec)
    (oracle : Fin nC → Spec.Bytes → Spec.Bytes) (Q : Nat) (hQ : Q ≤ 2 ^ 64)
    (hPos : 0 < n) (π : Spec.CoinSplit n nC nA)
    (prover : Fin nA → Spec.Code Spec.byteOracleIface
      (Spec.AggregateStatement AggValidatorPk nVal × SuccinctWhirAggregateProof))
    (hSlots : PackedSlotGameBounds (nVal := nVal) logCells profile prof fr nodeDecode slotC oracle Q)
    (fail : Fin n → Bool)
    (hFail : ∀ ω : Fin n, fail ω = true →
      let H := oracle (π.chal ω)
      let r := Spec.aggregateRun H Q (prover (π.advc ω))
      (∀ u : Fin nVal, r.1.1.roster u = (custody u).state.pk) ∧
      verifySuccinctWhirAggregate logCells profile fr H r.1.1 r.1.2 = true ∧
      ∃ v : Fin nVal, r.1.1.bitmap.getLsbD v.val = true ∧
        ¬ ((∃ b : Spec.AggregateBreak, Spec.TranscriptBreak H r.2 b) ∨
           Composed.QuorumForgery (profileGeom profile) (custody v) r.1.1.message ∨
           Composed.quorumParticipated (custody v) r.1.1.message = true)) :
    let ε := toSpecRatBound
      (RatBound.add (packedProdQromError logCells Q) (merkleProfileQromBound prof Q))
    Spec.GameBound (Spec.FinGame.mk hPos fail).winProb ε ∧
    ε.num * 2 ^ 128 < 1 * ε.den := by
  intro ε
  obtain ⟨hSound, hLt128⟩ :=
    succinctWhirAggregate_extractorSound logCells profile prof hLo hHi fr nodeDecode slotC oracle Q hQ hSlots
  refine ⟨hSound.failure_bound hPos π prover fail (fun ω hF => ?_), hLt128⟩
  obtain ⟨hRoster, hAcc, v, hAct, hNoOut⟩ := hFail ω hF
  refine ⟨hAcc, fun hOut => hNoOut ?_⟩
  rcases hOut.signer_trichotomy
      (fun u => Composed.quorumParticipated (custody u)
        (Spec.aggregateRun (oracle (π.chal ω)) Q (prover (π.advc ω))).1.1.message)
      v hAct with hBrk | ⟨sig, _, hSigVer, hq⟩ | hPart
  · exact .inl hBrk
  · rw [hRoster v] at hSigVer
    exact .inr (.inl ⟨sig, hSigVer, hq⟩)
  · exact .inr (.inr hPart)

/-! The finite-game witness needs actual codecs for all possible tables and messages.
    Lengths are unbounded LEB128 naturals. Products use sequential prefix parsing. -/
private class AuditFrame (α : Type) where
  codec : Spec.FramedCodec α

private instance : AuditFrame Nat := ⟨⟨leb128, Aggregation.decodeLeb128, Aggregation.decodeLeb128_leb128⟩⟩
private instance : AuditFrame UInt8 := ⟨.ofFixed FixedCodec.u8⟩
private instance {α β : Type} [AuditFrame α] [AuditFrame β] : AuditFrame (α × β) :=
  ⟨.pair AuditFrame.codec AuditFrame.codec⟩

@[instance_reducible] private def frameFrom {α β : Type} [AuditFrame β] (pack : α → β) (unpack : β → α)
    (roundTrip : ∀ x, unpack (pack x) = x) : AuditFrame α :=
  let c : Spec.FramedCodec β := AuditFrame.codec
  ⟨⟨fun a => c.encode (pack a), fun bs => (c.decodePrefix bs).map (Prod.map unpack id),
    fun a rest => by rw [c.decodePrefix_append]; simp [roundTrip]⟩⟩

private def readFrameList {α : Type} (c : Spec.FramedCodec α) :
    Nat → Spec.Bytes → Option (List α × Spec.Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (x, rest) ← c.decodePrefix bs
    let (xs, tail) ← readFrameList c n rest
    return (x :: xs, tail)

private theorem readFrameList_encode {α : Type} (c : Spec.FramedCodec α) (xs : List α) (bs : Spec.Bytes) :
    readFrameList c xs.length (xs.flatMap c.encode ++ bs) = some (xs, bs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [readFrameList, List.append_assoc, c.decodePrefix_append, ih]

private instance {α : Type} [AuditFrame α] : AuditFrame (List α) :=
  let c : Spec.FramedCodec α := AuditFrame.codec
  ⟨⟨fun xs => leb128 xs.length ++ xs.flatMap c.encode,
    fun bs => (Aggregation.decodeLeb128 bs).bind (fun (n, tail) => readFrameList c n tail),
    fun xs rest => by rw [List.append_assoc, Aggregation.decodeLeb128_leb128]; exact readFrameList_encode c xs rest⟩⟩

private instance {α : Type} [AuditFrame α] : AuditFrame (Option α) :=
  frameFrom Option.toList List.head? (fun x => by cases x <;> rfl)
private instance : AuditFrame (BitVec 256) :=
  frameFrom BitVec.toNat (BitVec.ofNat 256) (fun _ => by simp)
private instance : AuditFrame Goldilocks :=
  frameFrom Goldilocks.val Goldilocks.ofNat (fun x => Goldilocks.ext (Nat.mod_eq_of_lt x.isLt))
private instance : AuditFrame AggSigProfile :=
  frameFrom (fun | .xmssPoseidon2 => (0 : UInt8) | .corduroyPoseidon2 => 1)
    (fun b => if b = 0 then .xmssPoseidon2 else .corduroyPoseidon2) (fun p => by cases p <;> rfl)
private instance : AuditFrame Lane4 :=
  frameFrom (fun x => (x.x0, x.x1, x.x2, x.x3))
    (fun (x0, x1, x2, x3) => ⟨x0, x1, x2, x3⟩) (fun _ => rfl)
private instance : AuditFrame Poseidon2State12 :=
  frameFrom (fun x => (x.b0, x.b1, x.b2))
    (fun (b0, b1, b2) => ⟨b0, b1, b2⟩) (fun _ => rfl)
private instance : AuditFrame QuinticGoldilocks :=
  frameFrom (fun x => (x.c0, x.c1, x.c2, x.c3, x.c4))
    (fun (c0, c1, c2, c3, c4) => ⟨c0, c1, c2, c3, c4⟩) (fun _ => rfl)
private instance : AuditFrame AggValidatorPk :=
  frameFrom (fun x => (x.profile, x.pkSeed, x.pkRoot))
    (fun (profile, pkSeed, pkRoot) => ⟨profile, pkSeed, pkRoot⟩) (fun _ => rfl)
private instance : AuditFrame StepOpRow :=
  frameFrom (fun x => (x.stIn, x.initExtSbox, x.intSbox, x.termExtSbox, x.prevState, x.nextState, x.aux))
    (fun (stIn, initExtSbox, intSbox, termExtSbox, prevState, nextState, aux) => ⟨stIn, initExtSbox, intSbox, termExtSbox, prevState, nextState, aux⟩) (fun _ => rfl)
private instance : AuditFrame (WhirPub QuinticGoldilocks) :=
  frameFrom (fun x => (x.poly, x.answers))
    (fun (poly, answers) => ⟨poly, answers⟩) (fun _ => rfl)
private instance : AuditFrame PackedRound :=
  frameFrom (fun x => (x.root, x.pub))
    (fun (root, pub) => ⟨root, pub⟩) (fun _ => rfl)
private instance : AuditFrame WhirFsContext :=
  frameFrom (fun x => (x.logCells, x.profile, x.roster, x.bitmap, x.message, x.salt, x.slotRoot, x.whirRoot, x.claim))
    (fun (logCells, profile, roster, bitmap, message, salt, slotRoot, whirRoot, claim) => ⟨logCells, profile, roster, bitmap, message, salt, slotRoot, whirRoot, claim⟩) (fun _ => rfl)

private def auditWhirFraming : SuccinctWhirByteFraming :=
  ⟨AuditFrame.codec, AuditFrame.codec, AuditFrame.codec, AuditFrame.codec, (fun n => (n - 1).log2 + (if n ≤ 1 then 0 else 1))⟩

private def auditSlotCodec : SlotLeafTableCodec :=
  let c := taggedWhirFrame 4 (AuditFrame.codec (α := BitVec 256 × AggSigProfile × Nat × List StepOpRow))
  ⟨fun salt profile idx rows => c.encode (salt, profile, idx, rows),
    fun bs => (c.decodePrefix bs).bind (fun (leaf, tail) => if tail.isEmpty then some leaf else none),
    fun salt profile idx rows => by
      have h := c.decodePrefix_append (salt, profile, idx, rows) []
      rw [List.append_nil] at h
      rw [h]; rfl⟩

private def auditSqueeze : Spec.Bytes := List.replicate (packedChallengeBits / 8) 0

/-- In a one-validator tree the recorded leaf digest is the root. -/
theorem extractRecordedSingleton (profile : AggSigProfile) (fr : SuccinctWhirByteFraming)
    (depth : fr.slotTreeDepth 1 = 0) (slotC : SlotLeafTableCodec)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (stmt : Spec.AggregateStatement AggValidatorPk 1) (p : SuccinctWhirAggregateProof)
    (rows : List StepOpRow) (i : Fin 1) :
    extractSuccinctWhirAggregate profile fr nodeDecode slotC
      [(slotC.encode p.salt profile 0 rows, p.slotCommitRoot)] stmt p i =
      some (extractSlotNativeSig profile rows 0) := by
  simp [extractSuccinctWhirAggregate, recordedSlotRows, depth, extractOnlineMerkleOpening,
    Nat.lt_one_iff.mp i.isLt, slotC.decode_encode, List.findSome?]

/-- Honest single-validator recording and extraction. At depth zero the salted leaf digest
    is itself the root. The signer supplies the valid counters required by XMSS signing. -/
theorem inhabited_active_slot_extraction (fr : SuccinctWhirByteFraming) (depth : fr.slotTreeDepth 1 = 0)
    (slotC : SlotLeafTableCodec) (salt : BitVec 256) (H : Spec.Bytes → Spec.Bytes)
    (ctrs : ValidSigningCtrs xmssPoseidon2Geom auditSkSeed
      (deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed) auditMsg auditRRand 0) :
    let pk := deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed
    let signed := signAggNative xmssPoseidon2Geom auditSkSeed pk auditMsg auditRRand 0
      ctrs.layer0Ctr ctrs.upperCtrs
    let rows := stepXmssRows pk (computeMessageMu pk auditMsg) signed
    let stmt : Spec.AggregateStatement AggValidatorPk 1 := ⟨fun _ => pk, 1#1, auditMsg⟩
    let leaf := slotC.encode salt .xmssPoseidon2 0 rows
    let finish := fun digest => (stmt, (⟨salt, digest, [], QuinticGoldilocks.one, [], [], []⟩ :
      SuccinctWhirAggregateProof))
    let r := Spec.aggregateRun H 1 (.call leaf (fun digest => .ret (finish digest)))
    let sigs := extractSuccinctWhirAggregate .xmssPoseidon2 fr (fun _ => none) slotC r.2 r.1.1 r.1.2
    r.2 = [(leaf, H leaf)] ∧ sigs 0 = some (extractSlotNativeSig .xmssPoseidon2 rows 0) ∧
      Spec.ValidAggregateWitness (verifyAggNativeSig (profileGeom .xmssPoseidon2)) stmt sigs := by
  intro pk signed rows stmt leaf finish r sigs
  have hr : r = (finish (H leaf), [(leaf, H leaf)]) := Spec.aggregateRun_one_call (by decide : 1 ≤ 1) H leaf finish
  have hs (i : Fin 1) : sigs i = some (extractSlotNativeSig .xmssPoseidon2 rows 0) := by
    change extractSuccinctWhirAggregate .xmssPoseidon2 fr _ slotC r.2 r.1.1 r.1.2 i = _
    rw [hr]
    exact extractRecordedSingleton _ fr depth slotC _ stmt (finish (H leaf)).2 rows i
  have hv := (inhabited_aggNativeSig_euf_cma_pipeline.2.2.2 ctrs).1
  exact ⟨congrArg Prod.snd hr, hs 0, Spec.ValidAggregateWitness.intro (fun i _ =>
    ⟨_, hs i, singleSlot_stepOp256_extract .xmssPoseidon2 (.inl rfl) pk auditMsg rows
      (stepXmssNative_profile pk auditMsg signed hv) (stepXmssRows_of_verify pk auditMsg signed hv)⟩)⟩

/-! ## §5. Aggregate extractor negative control -/

/-- The negative control retains the entire envelope and Fiat–Shamir parsing. -/
def verifySuccinctWhirOmitQueriesAndOod {nVal : Nat} (logCells : Nat) (profile : AggSigProfile)
    (fr : SuccinctWhirByteFraming) (H : Spec.Bytes → Spec.Bytes)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (p : SuccinctWhirAggregateProof) : Bool :=
  packedEnvelopeOk logCells profile fr H stmt p &&
    (deriveSuccinctFsTranscript fr H (whirContext logCells profile stmt p) p.rounds).isSome

private theorem deriveFsAux_total (fr : SuccinctWhirByteFraming) (H : Spec.Bytes → Spec.Bytes)
    (width : ∀ bs, (H bs).length = packedChallengeBits / 8) (ctx : WhirFsContext)
    (pre rounds : List PackedRound) : (deriveFsAux fr H ctx pre rounds).isSome = true := by
  induction rounds generalizing pre with
  | nil => rfl
  | cons m ms ih =>
    cases ht : deriveFsAux fr H ctx (pre ++ [m]) ms with
    | none => simpa [ht] using ih (pre ++ [m])
    | some t => simp [deriveFsAux, whirPrefixChallenge, width, ht]

/-- A singleton context query carries no signature when both of its byte strings
    are disjoint from the slot-leaf codec. -/
theorem contextOnly_extract_none {nVal : Nat} (slotC : SlotLeafTableCodec)
    (extract : List (Spec.Bytes × Spec.Bytes) → Spec.AggregateStatement AggValidatorPk nVal →
      SuccinctWhirAggregateProof → Fin nVal → Option AggNativeSignature)
    (straight : Spec.StraightLineExtractor (decodeSlotLeafSig slotC) succinctWhirProofSigs extract)
    (x y : Spec.Bytes) (hx : slotC.decode x = none) (hy : slotC.decode y = none)
    (stmt : Spec.AggregateStatement AggValidatorPk nVal) (p : SuccinctWhirAggregateProof) (i : Fin nVal) :
    extract [(x, y)] stmt p i = none := by
  cases hs : extract [(x, y)] stmt p i with
  | none => rfl
  | some sig =>
    have h := (Spec.StraightLineExtractor_iff ..).mp straight [(x,y)] stmt p i sig hs
    simp [succinctWhirProofSigs, decodeSlotLeafSig, hx, hy] at h

/-- Removing the inner verdict leaves a structural language that admits an active signer
    with no recorded slot preimage. A single funded query suffices on every challenger coin. -/
theorem tooth_omitted_stage0_queries_or_ood_accepts_bogus_table {nC : Nat} (hPos : 0 < nC)
    (logCells : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) (profile : AggSigProfile)
    (fr : SuccinctWhirByteFraming) (slotC : SlotLeafTableCodec)
    (tag : ∀ bs, slotC.decode (0 :: bs) = none)
    (extract : List (Spec.Bytes × Spec.Bytes) → Spec.AggregateStatement AggValidatorPk 1 →
      SuccinctWhirAggregateProof → Fin 1 → Option AggNativeSignature)
    (oracle : Fin nC → Spec.Bytes → Spec.Bytes) (width : ∀ c bs, (oracle c bs).length = packedChallengeBits / 8)
    (answer : ∀ c bs, slotC.decode (oracle c bs) = none) (Q : Nat) (hQ : 1 ≤ Q)
    {ε : Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ Spec.AggregateExtractorSound
      (Spec.StraightLineExtractor (decodeSlotLeafSig slotC) succinctWhirProofSigs)
      (verifyAggNativeSig (profileGeom profile)) (verifySuccinctWhirOmitQueriesAndOod logCells profile fr)
      extract oracle Q ε := by
  intro sound
  let stmt : Spec.AggregateStatement AggValidatorPk 1 :=
    ⟨fun _ => ⟨profile, auditPkSeed, auditPkSeed⟩, 1#1, auditMsg⟩
  let stages := packedProdStages logCells
  let roundAt := fun r => (⟨(stageOfCommitRound stages r).bind
    (fun j => if j + 1 < stages.length then some [1] else none), ⟨[], []⟩⟩ : PackedRound)
  let rounds := (List.range (packedProdSched logCells).numRounds).map roundAt
  have roots : packedRootsPresent stages rounds = true := by
    apply List.all_eq_true.mpr
    rintro ⟨m,r⟩ hm
    obtain ⟨hr, he⟩ := List.mem_zipIdx' hm
    have eq : m = roundAt r := by simpa [rounds] using he
    subst m
    cases h : stageOfCommitRound stages r with
    | none => simp [roundAt, h]
    | some j => by_cases hj : j + 1 < stages.length <;> simp [roundAt, h, hj]
  let proof := fun digest => (⟨0#256, [1], [1], QuinticGoldilocks.one, rounds, [], digest⟩ :
    SuccinctWhirAggregateProof)
  let ctx := whirContext logCells profile stmt (proof [])
  let x : Spec.Bytes := 0 :: fr.contextC.encode ctx
  let finish := fun digest => (stmt, proof digest)
  let prog : Spec.Code Spec.byteOracleIface _ := .call x (fun digest => .ret (finish digest))
  let π := Spec.CoinSplit.challengerOnly nC
  apply Spec.FinGame.not_bound_of_forall_win (Spec.FinGame.mk hPos (fun _ => true)) (fun _ => rfl) hε
  apply sound.failure_bound hPos π (fun _ => prog)
  intro ω _
  let c := π.chal ω
  have hr := Spec.aggregateRun_one_call hQ (oracle c) x finish
  change verifySuccinctWhirOmitQueriesAndOod logCells profile fr (oracle c)
    (Spec.aggregateRun (oracle c) Q prog).1.1 (Spec.aggregateRun (oracle c) Q prog).1.2 = true ∧ _
  change Spec.aggregateRun (oracle c) Q prog = _ at hr
  rw [hr]
  let p := proof (oracle c x)
  change verifySuccinctWhirOmitQueriesAndOod logCells profile fr (oracle c) stmt p = true ∧
    ¬ Spec.AggregateSoundnessOutcome _ (oracle c) [(x, oracle c x)] stmt (extract [(x, oracle c x)] stmt p)
  constructor
  · have profiles : (List.finRange 1).all (fun i => !stmt.bitmap.getLsbD i.val ||
        (stmt.roster i).profile == profile) = true := List.all_eq_true.mpr (fun _ _ => by simp [stmt])
    have transcript := deriveFsAux_total fr (oracle c) (width c) ctx [] rounds
    change (packedEnvelopeOk logCells profile fr (oracle c) stmt p && (deriveFsAux fr (oracle c) ctx [] rounds).isSome) = true
    rw [transcript, Bool.and_true]
    unfold packedEnvelopeOk
    simp only [profiles, p, proof, hLo, hHi, Nat.zero_lt_succ, and_self, decide_true,
      List.cons_ne_nil, ne_eq, not_false_eq_true, Bool.true_and, rounds, List.length_map, List.length_range]
    simpa [x, ctx, proof, whirContext, stages, rounds] using roots
  · intro outcome
    rcases (Spec.AggregateSoundnessOutcome_iff ..).mp outcome with valid | ⟨b, hb⟩
    · obtain ⟨_, hs, _⟩ := (Spec.ValidAggregateWitness_iff ..).mp valid 0 (show (1#1).getLsbD 0 = true by decide)
      rw [contextOnly_extract_none slotC extract sound.1 x (oracle c x) (tag _) (answer c x) stmt p 0] at hs
      contradiction
    · have collision := Spec.transcriptCollision_complete (oracle c) [(x, oracle c x)]
        (by simp) hb
      rw [Spec.transcriptCollision_singleton] at collision
      contradiction

theorem inhabited_tooth_omitted_stage0_queries_or_ood :
    ∃ (fr : SuccinctWhirByteFraming) (slotC : SlotLeafTableCodec)
      (oracle : Fin 1 → Spec.Bytes → Spec.Bytes),
      (∀ bs, slotC.decode (0 :: bs) = none) ∧
      (∀ c bs, (oracle c bs).length = packedChallengeBits / 8) ∧
      (∀ c bs, slotC.decode (oracle c bs) = none) ∧
      ¬ Spec.AggregateExtractorSound
        (Spec.StraightLineExtractor (decodeSlotLeafSig slotC) succinctWhirProofSigs)
        (verifyAggNativeSig (profileGeom .xmssPoseidon2))
        (verifySuccinctWhirOmitQueriesAndOod (nVal := 1) 16 .xmssPoseidon2 fr)
        (extractSuccinctWhirAggregate (nVal := 1) .xmssPoseidon2 fr (fun _ => none) slotC)
        oracle 1 (Spec.RatBound.invPow2 128) := by
  refine ⟨auditWhirFraming, auditSlotCodec, fun _ _ => auditSqueeze,
    fun _ => rfl, fun _ _ => List.length_replicate, fun _ _ => rfl, ?_⟩
  exact tooth_omitted_stage0_queries_or_ood_accepts_bogus_table Nat.one_pos 16
    (Nat.le_refl 16) (by decide) .xmssPoseidon2 auditWhirFraming auditSlotCodec
    (fun _ => rfl) _ (fun _ _ => auditSqueeze) (fun _ _ => List.length_replicate)
    (fun _ _ => rfl) 1 (Nat.le_refl 1) (by decide)

#verify_kernel packedBridge

#verify_constructive extractRecordedSingleton
  inhabited_tooth_omitted_stage0_queries_or_ood
  deriveFsAux_total contextOnly_extract_none readFrameList_encode inhabited_active_slot_extraction
  slotSignaturesRecovered_reconstructed packedSlotGameBounds_of_reconstructed
  measuredSuccinctWhirAggregate_extractorSound measuredSuccinctWhirAggregate_refines_idealAggregate
  zkHemV2MultiStage_qrom_soundness_128 realized_challenge realized_transcript realized_merkle packedByteEvent_accept
  packedWhir_qrom_soundness_128 succinctWhirAggregate_qrom_soundness_128
  validExtractedSlots finRange_getElem?_local succinctCommitteeSlots_getElem? stepOp256TableOk_bothProfiles_extract
  singleSlot_stepOp256_extract SlotLeafTableCodec.encode_inj decodeSlotLeafSig_encode
  deriveFsAux_eq verifySuccinctWhirAggregate_finite_accept
  packedQueries_stage_lt whirRoundPreimage_injective changed_message_round_addresses changed_message_collision verifySuccinctWhirAggregate_context tooth_changed_message_rejected
  extractSuccinctWhirAggregate_straightLine succinctWhirAggregate_extractorSound
  succinctWhirAggregate_refines_idealAggregate_128
  succinctWhirAggregate_quorum_euf_cma_reduction tooth_omitted_stage0_queries_or_ood_accepts_bogus_table


#tooth_pair verifySuccinctWhirAggregate_context vs tooth_changed_message_rejected
#tooth_pair succinctWhirAggregate_extractorSound vs tooth_omitted_stage0_queries_or_ood_accepts_bogus_table

end Qsag.SuccinctWhirAgg
end

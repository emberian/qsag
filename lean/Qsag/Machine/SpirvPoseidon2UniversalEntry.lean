module
public import Qsag.Machine.SpirvPoseidon2FullEquiv
public import Qsag.Oracle.Poseidon2

/-! Arbitrary-state refinement of the decoded width-12 entry. The word-level
    summaries retain the SPIR-V truncations. The control-flow reduction is
    parametric in the four operations on the round path. -/
namespace Qsag.Spv
namespace Universal
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private theorem doubleField (x : Goldilocks) : x.add x = (Goldilocks.ofNat 2).mul x := by
  apply Goldilocks.ext
  rw [Goldilocks.add_val, Goldilocks.mul_val, ← Nat.two_mul]
  rfl

private theorem matrixField (a b c d : Goldilocks) :
    rawM4 ⟨a.val,b.val,c.val,d.val⟩ = laneWords (applyM4 ⟨a,b,c,d⟩) := by
  simp only [rawM4, matrix4.public_eqs, laneWords.public_eqs, applyM4_eq, lane4Sum_eq, clipField, addField, doubleField]

/-- All four pointer copy-outs of the deployed M4 call. -/
public theorem spirv_poseidon2_m4 (w : World Unit) (b : Lane4) (g : Glob Unit) :
    (callFn p2 w 1100 8 50 [.n b.x0.val,.n b.x1.val,.n b.x2.val,.n b.x3.val] g).map
      (fun r => r.2.1) = some ((applyM4 b).toList.map (fun x => .n x.val)) := by
  rw [call_m4_words]
  have h := matrixField b.x0 b.x1 b.x2 b.x3
  rw [laneWords.public_eqs b, h]
  simp only [W4.vals.public_eqs, laneWords.public_eqs, Lane4.toList_eq, List.map_cons, List.map_nil]

private theorem externalField (s : Poseidon2State12) : rawME (stateWords s) = stateWords (applyME s) := by
  simp only [rawME, externalLayer.public_eqs, stateWords.public_eqs, applyME, applyMEStd, poseidon2Transpose3x4_eq,
    poseidon2Transpose4x3_eq, lane4Add_eq, clipField, redField, matrixField, laneWords.public_eqs, addField]

private theorem addAssoc (x y z : Goldilocks) : (x.add y).add z = x.add (y.add z) :=
  LawfulCommRing.add_assoc x y z

private theorem negScale (x : Goldilocks) :
    ((Goldilocks.ofNat 64).mul x).neg = (goldOfInt (-64)).mul x := by
  have h : goldOfInt (-64) = (Goldilocks.ofNat 64).neg := by decide +kernel
  rw [h]
  change CommRingOps.neg (CommRingOps.mul _ _) = CommRingOps.mul (CommRingOps.neg _) _
  constructive_ring

private theorem internalField (s : Poseidon2State12) : rawMI (stateWords s) = stateWords (applyMI s) := by
  simp (disch := decide) only [rawMI, internalLayer.public_eqs, stateWords.public_eqs, applyMI, state12Sum.public_eqs,
    lane4Sum_eq, clipField, addZero, addField, shiftField, negField, Nat.reducePow, negScale, addAssoc]
  rfl

private theorem extRoundField (rc s : Poseidon2State12) :
    wordExternal addWords seventhWord rawME rc (stateWords s) = stateWords (externalRound rc s) := by
  rw [wordExternal.public_eqs, externalRound_eq]
  simp only [stateWords.public_eqs, clipField, addField, boxField]
  simpa only [stateWords.public_eqs, sboxState12_eq, state12Add_eq, lane4Add_eq] using externalField (sboxState12 (state12Add s rc))

private theorem intRoundField (rc : Goldilocks) (s : Poseidon2State12) :
    wordInternal addWords seventhWord rawMI rc (stateWords s) = stateWords (internalRound rc s) := by
  rw [wordInternal.public_eqs, internalRound_eq]
  simp only [stateWords.public_eqs, clipField, addField, boxField]
  simpa only [stateWords.public_eqs] using internalField ⟨⟨sbox7 (s.b0.x0.add rc),s.b0.x1,s.b0.x2,s.b0.x3⟩,s.b1,s.b2⟩

private theorem roundsField {C : Type} (f : C → W12 → W12) (g : C → Poseidon2State12 → Poseidon2State12)
    (h : ∀ c s, f c (stateWords s) = stateWords (g c s)) (cs : List C) (s : Poseidon2State12) :
    runRounds f cs (stateWords s) = stateWords (runRounds g cs s) := by
  induction cs generalizing s with
  | nil => simp only [runRounds_nil]
  | cons c cs ih => simp only [runRounds_cons, h, ih]

private def readState (s : Poseidon2State12) (i : Nat) : Nat :=
  ((stateWords s).words).getD i 0

private theorem roundsCorrect (s : Poseidon2State12) :
    wordRounds addWords seventhWord rawME rawMI (readState s) = stateWords (poseidon2Perm12 s) := by
  rw [wordRounds.public_eqs]
  unfold poseidon2Perm12
  have start : W12.mk
      (clip (readState s 0)) (clip (readState s 1)) (clip (readState s 2)) (clip (readState s 3))
      (clip (readState s 4)) (clip (readState s 5)) (clip (readState s 6)) (clip (readState s 7))
      (clip (readState s 8)) (clip (readState s 9)) (clip (readState s 10)) (clip (readState s 11)) = stateWords s := by
    simp only [readState, stateWords.public_eqs, W12.words.public_eqs, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, clipField]
  simp only [start, externalField, roundsField _ _ extRoundField, roundsField _ _ intRoundField]

private theorem finalWords (s : Poseidon2State12) :
    (stateWords s).words.map clip = s.toList.map (·.val) := by
  simp only [stateWords.public_eqs, W12.words.public_eqs, Poseidon2State12.toList_eq, List.map_cons, List.map_nil, clipField]

/-- A single active invocation, with the first state at offset zero. All twelve
    output words, including their destination root, member, index and order. -/
public theorem spirv_poseidon2_perm12_entry_universal (s : Poseidon2State12) :
    decode poseidon2Perm12SpvWords = some p2 ∧
    poseidonEntryStores p2 (fun i => (s.toList.map (·.val)).getD i 0) =
      some (expectedStores ((poseidon2Perm12 s).toList.map (·.val))) := by
  refine ⟨p2_decoded, ?_⟩
  have words (t : Poseidon2State12) : (stateWords t).words = t.toList.map (·.val) := by
    simp only [stateWords.public_eqs, W12.words.public_eqs, Poseidon2State12.toList_eq, List.map_cons, List.map_nil]
  rw [← words s]
  change poseidonEntryStores p2 (readState s) = _
  rw [entry_word_rounds, roundsCorrect, finalWords]

#print axioms spirv_poseidon2_m4
#print axioms spirv_poseidon2_perm12_entry_universal

public def stateOfLanes (st : Fin 12 → Goldilocks) : Poseidon2State12 :=
  ⟨⟨st 0, st 1, st 2, st 3⟩, ⟨st 4, st 5, st 6, st 7⟩, ⟨st 8, st 9, st 10, st 11⟩⟩

public theorem spirv_poseidon2_perm12_fin12 (st : Fin 12 → Goldilocks) :
    poseidonEntryStores p2 (fun i => if h : i < 12 then (st ⟨i,h⟩).val else 0) =
      some (expectedStores ((poseidon2Perm12 (stateOfLanes st)).toList.map (·.val))) := by
  have e : (fun i => if h : i < 12 then (st ⟨i,h⟩).val else 0) =
      (fun i => ((stateOfLanes st).toList.map (·.val)).getD i 0) := by
    funext i
    rw [Poseidon2State12.toList_eq]
    rcases i with _|_|_|_|_|_|_|_|_|_|_|_|i <;> first | rfl | rw [dif_neg (by omega)]; rfl
  rw [e]
  exact (spirv_poseidon2_perm12_entry_universal _).2

#print axioms spirv_poseidon2_perm12_fin12

end Universal
end Qsag.Spv

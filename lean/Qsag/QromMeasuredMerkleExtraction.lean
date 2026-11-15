module
/-
# Merkle opening extraction in the measured-query experiment

The classical pre-challenge extractor `extractOnlineMerkleOpening` is run on the records
produced by the measured-query experiment of `QromMeasuredQueryExperiment`: the record list
is computed from the measured addresses and their oracle answers, through an explicit
address layout. No query table, consistency proof or event cover is supplied from outside.

Main result `measured_merkle_extraction_failure_bound`: for a uniformly random oracle, the
mass of outputs whose opening verifies against the oracle but differs from the opening
extracted from the measured log is at most

    (d * (3 * Q + 1) + (0 + 1 + ... + (Q - 1))) / 2^w

of the total mass, for paths of length at most `d`.

Requirements on the layout (deployment obligations, stated as structure fields): decoding
is sound, and encoding is injective on the `levels × nodes` tweak range, which is the
domain separation between tree positions and from any other use of the oracle.

Scope. This is a theorem about adversaries whose oracle queries are observed. It does not
bound a coherent-query adversary (see `measured_parity_execution`); for that case the
missing component is still an extraction experiment with a proved disturbance bound.
-/

public import Qsag.QromMeasuredQueryExperiment
import all Qsag.QromMeasuredQueryExperiment
import all Qsag.QromMerkleOnlineExtraction
import all Qsag.MultiRoundFsQrom
import all Qsag.ConcreteSecurityBudget

public section
namespace Qsag

set_option autoImplicit false

/-! ## Address layout and records -/

/-- How Merkle compression inputs `(lvl, node, left, right)` occupy oracle addresses.
    Addresses that are not compression inputs decode to `none`. -/
structure MerkleAddressLayout (cardX w : Nat) where
  encode : Nat → Nat → BitVec w → BitVec w → Fin cardX
  decode : Fin cardX → Option (Nat × Nat × BitVec w × BitVec w)
  levels : Nat
  nodes : Nat
  decode_sound : ∀ x l n u v, decode x = some (l, n, u, v) → encode l n u v = x
  decode_encode : ∀ l n u v, l < levels → n < nodes →
    decode (encode l n u v) = some (l, n, u, v)

/-- The tweaked compression function read through the layout. -/
def MerkleAddressLayout.hash {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) : Nat → Nat → BitVec w → BitVec w → BitVec w :=
  fun l n u v => H (L.encode l n u v)

/-- The classical record of one measured query, if its address is a compression input. -/
def merkleRecordOf {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (x : Fin cardX) : Option (RecordedMerkleQuery (BitVec w)) :=
  match L.decode x with
  | none => none
  | some (l, n, u, v) => some ⟨l, n, u, v, H x⟩

/-- Records of a measured query log. -/
def merkleRecords {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) :
    List (RecordedMerkleQuery (BitVec w)) :=
  xs.filterMap (merkleRecordOf L H)

theorem merkleRecordOf_some {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (x : Fin cardX) (q : RecordedMerkleQuery (BitVec w))
    (h : merkleRecordOf L H x = some q) :
    L.decode x = some (q.lvl, q.node, q.left, q.right) ∧ q.out = H x := by
  unfold merkleRecordOf at h
  cases hd : L.decode x with
  | none => rw [hd] at h; cases h
  | some τ =>
    obtain ⟨l, n, u, v⟩ := τ
    rw [hd] at h
    have h' : some (⟨l, n, u, v, H x⟩ : RecordedMerkleQuery (BitVec w)) = some q := h
    cases h'
    exact ⟨rfl, rfl⟩

/-- The records satisfy the classical classifier's consistency premise. It is derived from
    the measured log and the layout, not assumed. -/
theorem merkleRecords_consistent {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) :
    ∀ q ∈ merkleRecords L H xs, merkleQueryConsistent (L.hash H) q := by
  intro q hq
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.mp hq
  obtain ⟨hDec, hOut⟩ := merkleRecordOf_some L H x q hx
  show H (L.encode q.lvl q.node q.left q.right) = q.out
  rw [L.decode_sound x _ _ _ _ hDec, hOut]

private theorem listHasElem_false_cons {α : Type} [DecidableEq α] {x y : α} {ys : List α}
    (h : listHasElem x (y :: ys) = false) : y ≠ x ∧ listHasElem x ys = false := by
  refine ⟨fun he => Bool.noConfusion (h.symm.trans
    ((listHasElem_eq_true_iff x (y :: ys)).mpr (he ▸ .head ys))), ?_⟩
  cases hc : listHasElem x ys
  · rfl
  · exact Bool.noConfusion (h.symm.trans ((listHasElem_eq_true_iff x (y :: ys)).mpr
      (.tail y ((listHasElem_eq_true_iff x ys).mp hc))))

private theorem not_mem_of_listHasElem_false {α : Type} [DecidableEq α] {x : α} {ys : List α}
    (h : listHasElem x ys = false) : x ∉ ys :=
  fun hm => Bool.noConfusion (h.symm.trans ((listHasElem_eq_true_iff x ys).mpr hm))

/-- Records do not change when the oracle is reprogrammed at an unmeasured address. -/
theorem merkleRecords_reprogram_of_fresh {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (a : Fin cardX) (ch : BitVec w) :
    ∀ (xs : List (Fin cardX)), listHasElem a xs = false →
      merkleRecords L (reprogramOracle H a ch) xs = merkleRecords L H xs
  | [], _ => rfl
  | y :: ys, h => by
    obtain ⟨hya, hTail⟩ := listHasElem_false_cons h
    have hRec : merkleRecordOf L (reprogramOracle H a ch) y = merkleRecordOf L H y := by
      unfold merkleRecordOf
      rw [reprogramOracle_of_ne H a ch y hya]
    have ih := merkleRecords_reprogram_of_fresh L H a ch ys hTail
    unfold merkleRecords at ih ⊢
    rw [List.filterMap_cons, List.filterMap_cons, hRec, ih]

/-! ## The verifier's evaluation addresses -/

/-- Oracle addresses evaluated by `merkleRootFromPath` through the layout, leaf side first. -/
def merklePathPoints {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) : Nat → Nat → BitVec w → List (BitVec w) → List (Fin cardX)
  | _, _, _, [] => []
  | lvl, idx, cur, sib :: rest =>
    L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib) (if idx % 2 = 0 then sib else cur) ::
      merklePathPoints L H (lvl + 1) (idx / 2)
        (H (L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
          (if idx % 2 = 0 then sib else cur))) rest

theorem merklePathPoints_length {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) : ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w),
    (merklePathPoints L H lvl idx cur path).length = path.length
  | [], _, _, _ => rfl
  | _ :: rest, lvl, idx, _ =>
    congrArg Nat.succ (merklePathPoints_length L H rest (lvl + 1) (idx / 2) _)

/-- The root recomputation reads the oracle exactly along `merklePathPoints`. -/
theorem merkleRootFromPath_step {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (lvl idx : Nat) (cur sib : BitVec w) (rest : List (BitVec w)) :
    merkleRootFromPath (L.hash H) lvl idx cur (sib :: rest) =
      merkleRootFromPath (L.hash H) (lvl + 1) (idx / 2)
        (H (L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
          (if idx % 2 = 0 then sib else cur))) rest := by
  show merkleRootFromPath (L.hash H) (lvl + 1) (idx / 2)
    (if idx % 2 = 0 then L.hash H lvl (idx / 2) cur sib else L.hash H lvl (idx / 2) sib cur)
    rest = _
  by_cases hp : idx % 2 = 0
  · simp only [hp, ↓reduceIte, MerkleAddressLayout.hash]
  · simp only [hp, ↓reduceIte, MerkleAddressLayout.hash]

/-- Inside the tweak range, every evaluation address decodes to a level at or above the
    starting level. -/
theorem merklePathPoints_level {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) : ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w)
    (a : Fin cardX), lvl + path.length ≤ L.levels → idx < L.nodes →
    a ∈ merklePathPoints L H lvl idx cur path →
    ∃ τ, L.decode a = some τ ∧ lvl ≤ τ.1
  | [], _, _, _, _, _, _, ha => nomatch ha
  | sib :: rest, lvl, idx, cur, a, hLvl, hIdx, ha => by
    have hLen : (sib :: rest).length = rest.length + 1 := rfl
    have hl : lvl < L.levels := by omega
    have hn : idx / 2 < L.nodes := Nat.lt_of_le_of_lt (Nat.div_le_self idx 2) hIdx
    rcases List.mem_cons.mp ha with rfl | hTail
    · exact ⟨_, L.decode_encode lvl (idx / 2) _ _ hl hn, Nat.le_refl lvl⟩
    · obtain ⟨τ, hτ, hle⟩ := merklePathPoints_level L H rest (lvl + 1) (idx / 2) _ a
        (by omega) hn hTail
      exact ⟨τ, hτ, Nat.le_of_succ_le hle⟩

/-- Inside the tweak range, the `k`-th evaluation address is not changed by reprogramming
    the oracle at that address: it is computed from answers at strictly lower levels. -/
theorem merklePathPoints_reprogram {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (ch : BitVec w) :
    ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w) (k : Nat) (a : Fin cardX),
    lvl + path.length ≤ L.levels → idx < L.nodes →
    (merklePathPoints L H lvl idx cur path)[k]? = some a →
    (merklePathPoints L (reprogramOracle H a ch) lvl idx cur path)[k]? = some a
  | [], _, _, _, _, _, _, _, h => nomatch h
  | _ :: _, _, _, _, 0, _, _, _, h => h
  | sib :: rest, lvl, idx, cur, k + 1, a, hLvl, hIdx, h => by
    have hLen : (sib :: rest).length = rest.length + 1 := rfl
    have hl : lvl < L.levels := by omega
    have hn : idx / 2 < L.nodes := Nat.lt_of_le_of_lt (Nat.div_le_self idx 2) hIdx
    have hTail : (merklePathPoints L H (lvl + 1) (idx / 2)
        (H (L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
          (if idx % 2 = 0 then sib else cur))) rest)[k]? = some a := h
    have hMem := List.mem_of_getElem? hTail
    obtain ⟨τ, hτ, hle⟩ := merklePathPoints_level L H rest (lvl + 1) (idx / 2) _ a
      (by omega) hn hMem
    have hNe : L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
        (if idx % 2 = 0 then sib else cur) ≠ a := by
      intro he
      have hd := L.decode_encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
        (if idx % 2 = 0 then sib else cur) hl hn
      rw [he, hτ] at hd
      have hEq : τ.1 = lvl := congrArg Prod.fst (Option.some.inj hd)
      omega
    show (merklePathPoints L (reprogramOracle H a ch) (lvl + 1) (idx / 2)
        (reprogramOracle H a ch (L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
          (if idx % 2 = 0 then sib else cur))) rest)[k]? = some a
    rw [reprogramOracle_of_ne H a ch _ hNe]
    exact merklePathPoints_reprogram L H ch rest (lvl + 1) (idx / 2) _ k a (by omega) hn hTail

/-! ## Deterministic classification of an accepted opening -/

/-- Targets fixed by the measured log: the root, the children named in recorded inputs,
    and the recorded answers. -/
def merkleMeasuredTargets {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (rt : BitVec w) : List (BitVec w) :=
  rt :: (merkleChildTargets (merkleRecords L H xs) ++ xs.map H)

theorem merkleMeasuredTargets_length {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (rt : BitVec w) :
    (merkleMeasuredTargets L H xs rt).length ≤ 3 * xs.length + 1 := by
  have hRec : (merkleRecords L H xs).length ≤ xs.length := List.length_filterMap_le _ _
  simp only [merkleMeasuredTargets, List.length_cons, List.length_append,
    merkleChildTargets_length, List.length_map]
  omega

/-- An opening that verifies against the oracle either equals the opening extracted from
    the measured records, or the verifier evaluated an unmeasured address whose answer lies
    in the log-determined target list, or two distinct measured addresses share an answer.
    This uses only the layout laws; the records come from the log itself. -/
theorem merkle_measured_opening_classification {cardX w : Nat}
    (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) (xs : List (Fin cardX))
    (rt : BitVec w) :
    ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w),
    lvl + path.length ≤ L.levels → idx < L.nodes →
    merkleRootFromPath (L.hash H) lvl idx cur path = rt →
    extractOnlineMerkleOpening rt (merkleRecords L H xs) lvl path.length idx =
        some (cur, path) ∨
    (∃ a ∈ merklePathPoints L H lvl idx cur path, listHasElem a xs = false ∧
      listHasElem (H a) (merkleMeasuredTargets L H xs rt) = true) ∨
    freshCollision H xs = true
  | [], lvl, idx, cur, _, _, hRoot => by
    have hEq : cur = rt := hRoot
    subst hEq
    exact Or.inl rfl
  | sib :: rest, lvl, idx, cur, hLvl, hIdx, hRoot => by
    have hLen : (sib :: rest).length = rest.length + 1 := rfl
    have hl : lvl < L.levels := by omega
    have hn : idx / 2 < L.nodes := Nat.lt_of_le_of_lt (Nat.div_le_self idx 2) hIdx
    let lCh := if idx % 2 = 0 then cur else sib
    let rCh := if idx % 2 = 0 then sib else cur
    let a := L.encode lvl (idx / 2) lCh rCh
    let parent := H a
    have hRoot' : merkleRootFromPath (L.hash H) (lvl + 1) (idx / 2) parent rest = rt :=
      (merkleRootFromPath_step L H lvl idx cur sib rest).symm.trans hRoot
    have hDecA : L.decode a = some (lvl, idx / 2, lCh, rCh) :=
      L.decode_encode lvl (idx / 2) lCh rCh hl hn
    have hParentTarget : extractOnlineMerkleOpening rt (merkleRecords L H xs) (lvl + 1)
        rest.length (idx / 2) = some (parent, rest) →
        listHasElem parent (merkleMeasuredTargets L H xs rt) = true := by
      intro hExtUp
      refine (listHasElem_eq_true_iff _ _).mpr ?_
      cases rest with
      | nil =>
        have hPar : parent = rt := by
          simp only [List.length_nil, extractOnlineMerkleOpening, Option.some.injEq,
            Prod.mk.injEq] at hExtUp
          exact hExtUp.1.symm
        rw [hPar]
        exact .head _
      | cons s tl =>
        exact .tail _ (List.mem_append.mpr (Or.inl
          (extractOnlineMerkleOpening_succ_child rt (merkleRecords L H xs) (lvl + 1)
            tl.length (idx / 2) parent _ hExtUp)))
    rcases merkle_measured_opening_classification L H xs rt rest (lvl + 1) (idx / 2) parent
        (by omega) hn hRoot' with hExtUp | ⟨a', ha', hFresh, hHit⟩ | hColl
    · let pred := fun q : RecordedMerkleQuery (BitVec w) =>
        decide (q.lvl = lvl) && decide (q.node = idx / 2) && decide (q.out = parent)
      cases hFind : findFirst pred (merkleRecords L H xs) with
      | none =>
        -- the verifier's address was never measured, and its answer is a logged target
        have hFreshA : listHasElem a xs = false := by
          cases hc : listHasElem a xs
          · rfl
          · have haMem : a ∈ xs := (listHasElem_eq_true_iff a xs).mp hc
            have hRec : merkleRecordOf L H a = some ⟨lvl, idx / 2, lCh, rCh, parent⟩ := by
              unfold merkleRecordOf
              rw [hDecA]
            have hMemRec : (⟨lvl, idx / 2, lCh, rCh, parent⟩ : RecordedMerkleQuery (BitVec w)) ∈
                merkleRecords L H xs := List.mem_filterMap.mpr ⟨a, haMem, hRec⟩
            have hFalse := findFirst_none_spec pred hFind _ hMemRec
            simp only [pred, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
        exact Or.inr (Or.inl ⟨a, .head _, hFreshA, hParentTarget hExtUp⟩)
      | some q =>
        obtain ⟨hqMem, hqPred⟩ := findFirst_some_spec pred hFind
        simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hqPred
        obtain ⟨⟨hqLvl, hqNode⟩, hqOut⟩ := hqPred
        obtain ⟨x, hxMem, hxRec⟩ := List.mem_filterMap.mp hqMem
        obtain ⟨hDecX, hOutX⟩ := merkleRecordOf_some L H x q hxRec
        have hAns : H x = H a := hOutX.symm.trans hqOut
        by_cases hxa : x = a
        · -- the recorded query is the verifier's own evaluation: the opening is extracted
          rw [hxa, hDecA] at hDecX
          have hTup := Option.some.inj hDecX
          have hqL : q.left = lCh := (congrArg (fun τ => τ.2.2.1) hTup).symm
          have hqR : q.right = rCh := (congrArg (fun τ => τ.2.2.2) hTup).symm
          refine Or.inl ?_
          show extractOnlineMerkleOpening rt (merkleRecords L H xs) lvl (rest.length + 1) idx =
            some (cur, sib :: rest)
          unfold extractOnlineMerkleOpening
          rw [hExtUp]
          dsimp only
          rw [hFind]
          dsimp only
          by_cases hp : idx % 2 = 0
          · dsimp only [lCh, rCh] at hqL hqR
            simp only [hp, ↓reduceIte] at hqL hqR ⊢
            rw [hqL, hqR]
          · dsimp only [lCh, rCh] at hqL hqR
            simp only [hp, ↓reduceIte] at hqL hqR ⊢
            rw [hqL, hqR]
        · cases hc : listHasElem a xs with
          | true =>
            exact Or.inr (Or.inr (freshCollision_of_distinct_equal H xs x a hxMem
              ((listHasElem_eq_true_iff a xs).mp hc) hxa hAns))
          | false =>
            refine Or.inr (Or.inl ⟨a, .head _, hc, (listHasElem_eq_true_iff _ _).mpr ?_⟩)
            refine .tail _ (List.mem_append.mpr (Or.inr ?_))
            show H a ∈ xs.map H
            rw [← hAns]
            exact List.mem_map_of_mem hxMem
    · exact Or.inr (Or.inl ⟨a', .tail _ ha', hFresh, hHit⟩)
    · exact Or.inr (Or.inr hColl)

/-! ## The extraction-failure bound -/

/-- Opening read from the final measured output register. -/
structure MerkleOpeningReadout (w : Nat) where
  rt : BitVec w
  idx : Nat
  leaf : BitVec w
  path : List (BitVec w)

/-- The opening has the verifier's shape: path length at most `d`, index in range. -/
def merkleOpeningShape {cardX w : Nat} (L : MerkleAddressLayout cardX w) (d : Nat)
    (op : MerkleOpeningReadout w) : Bool :=
  decide (op.path.length ≤ d) && decide (op.idx < L.nodes)

/-- Extraction failure: the output opening has the verifier's shape and recomputes its
    root under the oracle, yet is not the opening extracted from the measured records. -/
def measuredMerkleFailure {cardX w : Nat} (L : MerkleAddressLayout cardX w) (lvl d : Nat)
    (opening : Fin cardX → MerkleOpeningReadout w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (o : Fin cardX) : Bool :=
  merkleOpeningShape L d (opening o) &&
  decide (merkleRootFromPath (L.hash H) lvl (opening o).idx (opening o).leaf (opening o).path =
    (opening o).rt) &&
  !decide (extractOnlineMerkleOpening (opening o).rt (merkleRecords L H xs) lvl
    (opening o).path.length (opening o).idx = some ((opening o).leaf, (opening o).path))

/-- The `k`-th verifier evaluation address of the output opening (the output address itself
    when the opening is misshapen or shorter than `k + 1`). -/
def merkleFailurePoint {cardX w : Nat} (L : MerkleAddressLayout cardX w) (lvl d k : Nat)
    (opening : Fin cardX → MerkleOpeningReadout w)
    (H : Fin cardX → BitVec w) (o : Fin cardX) : Fin cardX :=
  if merkleOpeningShape L d (opening o) = true then
    ((merklePathPoints L H lvl (opening o).idx (opening o).leaf (opening o).path)[k]?).getD o
  else o

/-- Targets for the `k`-th evaluation address (empty for a misshapen opening). -/
def merkleFailureTargets {cardX w : Nat} (L : MerkleAddressLayout cardX w) (d : Nat)
    (opening : Fin cardX → MerkleOpeningReadout w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (o : Fin cardX) : List (BitVec w) :=
  if merkleOpeningShape L d (opening o) = true then
    merkleMeasuredTargets L H xs (opening o).rt
  else []

theorem merkleFailurePoint_local {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (lvl d k : Nat) (hLvl : lvl + d ≤ L.levels)
    (opening : Fin cardX → MerkleOpeningReadout w)
    (H : Fin cardX → BitVec w) (o : Fin cardX) (ch : BitVec w) :
    merkleFailurePoint L lvl d k opening
      (reprogramOracle H (merkleFailurePoint L lvl d k opening H o) ch) o =
      merkleFailurePoint L lvl d k opening H o := by
  unfold merkleFailurePoint
  cases hShape : merkleOpeningShape L d (opening o) with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    simp only [merkleOpeningShape, Bool.and_eq_true, decide_eq_true_eq] at hShape
    have hRange : lvl + (opening o).path.length ≤ L.levels := by omega
    cases hk : (merklePathPoints L H lvl (opening o).idx (opening o).leaf (opening o).path)[k]? with
    | none =>
      have hLe := List.getElem?_eq_none_iff.mp hk
      rw [merklePathPoints_length] at hLe
      have hk' : (merklePathPoints L (reprogramOracle H o ch) lvl (opening o).idx
          (opening o).leaf (opening o).path)[k]? = none :=
        List.getElem?_eq_none_iff.mpr (by rw [merklePathPoints_length]; exact hLe)
      simp only [Option.getD_none, hk']
    | some a =>
      simp only [Option.getD_some]
      rw [merklePathPoints_reprogram L H ch _ lvl _ _ k a hRange hShape.2 hk]
      rfl

private theorem le_qsum_term {n : Nat} (f : Fin n → Nat) (k : Fin n) : f k ≤ qsum n f := by
  rw [← qsum_ite_eq n k (f k)]
  refine qsum_le_qsum (fun i => ?_)
  by_cases h : i = k
  · rw [ite_eq_left h, h]
    exact Nat.le_refl _
  · rw [ite_eq_right h]
    exact Nat.zero_le _

/-- Failure implies a fresh-address hit at one of the first `d` evaluation addresses, or a
    collision among measured answers. -/
theorem measuredMerkleFailure_cover {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (hLvl : lvl + d ≤ L.levels)
    (opening : Fin cardX → MerkleOpeningReadout w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (o : Fin cardX)
    (hFail : measuredMerkleFailure L lvl d opening H xs o = true) :
    (∃ k : Fin d,
      (!listHasElem (merkleFailurePoint L lvl d k.1 opening H o) xs &&
        listHasElem (H (merkleFailurePoint L lvl d k.1 opening H o))
          (merkleFailureTargets L d opening H xs o)) = true) ∨
    freshCollision H xs = true := by
  simp only [measuredMerkleFailure, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hFail
  obtain ⟨⟨hShape, hRoot⟩, hNot⟩ := hFail
  have hShape' := hShape
  simp only [merkleOpeningShape, Bool.and_eq_true, decide_eq_true_eq] at hShape'
  have hRange : lvl + (opening o).path.length ≤ L.levels := by omega
  rcases merkle_measured_opening_classification L H xs (opening o).rt (opening o).path lvl
      (opening o).idx (opening o).leaf hRange hShape'.2 hRoot with hExt | ⟨a, ha, hFresh, hHit⟩ | hC
  · exact absurd hExt hNot
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ha
    have hkLt : k < d := by
      have h1 := (List.getElem?_eq_some_iff.mp hk).1
      rw [merklePathPoints_length] at h1
      omega
    refine Or.inl ⟨⟨k, hkLt⟩, ?_⟩
    have hPt : merkleFailurePoint L lvl d k opening H o = a := by
      unfold merkleFailurePoint
      rw [ite_eq_left hShape, hk]
      rfl
    have hTg : merkleFailureTargets L d opening H xs o =
        merkleMeasuredTargets L H xs (opening o).rt := by
      unfold merkleFailureTargets
      rw [ite_eq_left hShape]
    show (!listHasElem (merkleFailurePoint L lvl d k opening H o) xs &&
      listHasElem (H (merkleFailurePoint L lvl d k opening H o))
        (merkleFailureTargets L d opening H xs o)) = true
    rw [hPt, hTg, hFresh, hHit]
    rfl
  · exact Or.inr hC

/-- **Merkle extraction-failure bound for the measured-query experiment.** For every
    `Q`-query adversary, layout and output readout, with the oracle uniform: the mass of
    outputs whose opening (path length at most `d`) verifies but is not the opening
    extracted from the measured query log is at most
    `(d * (3 * Q + 1) + triangleSum Q) / 2^w` of the total mass. In `RatBound.le` form this
    is `⟨failure mass, total⟩ ≤ ⟨d * (3 * Q + 1) + triangleSum Q, 2^w⟩`. -/
theorem measured_merkle_extraction_failure_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (hLvl : lvl + d ≤ L.levels)
    (opening : Fin cardX → MerkleOpeningReadout w) :
    2 ^ w * uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (measuredMerkleFailure L lvl d opening H xs)
          (measuredStateAt A H Q (Nat.le_refl Q) xs))) ≤
      (d * (3 * Q + 1) + triangleSum Q) *
        ((2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)) := by
  let Tot := (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)
  let ψ : (Fin cardX → BitVec w) → List (Fin cardX) → QVec cardX w cardAnc := fun H xs =>
    measuredStateAt A H Q (Nat.le_refl Q) xs
  let ev : Fin d → (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool :=
    fun k H xs o =>
      !listHasElem (merkleFailurePoint L lvl d k.1 opening H o) xs &&
        listHasElem (H (merkleFailurePoint L lvl d k.1 opening H o))
          (merkleFailureTargets L d opening H xs o)
  -- per-level fresh-address bound
  have hLevel : ∀ k : Fin d,
      2 ^ w * uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (ev k H xs) (ψ H xs))) ≤ (3 * Q + 1) * Tot := by
    intro k
    refine measured_fresh_target_hit_bound A
      (fun H _ o => merkleFailurePoint L lvl d k.1 opening H o)
      (fun H xs o => merkleFailureTargets L d opening H xs o) (3 * Q + 1)
      (fun H _ o ch => merkleFailurePoint_local L lvl d k.1 hLvl opening H o ch) ?_ ?_
    · intro H xs o ch hFresh
      unfold merkleFailureTargets
      cases merkleOpeningShape L d (opening o)
      · rfl
      · simp only [↓reduceIte, merkleMeasuredTargets]
        rw [merkleRecords_reprogram_of_fresh L H _ ch xs hFresh,
          map_reprogram_of_fresh H _ ch xs hFresh]
    · intro H xs o hLen
      unfold merkleFailureTargets
      cases merkleOpeningShape L d (opening o)
      · exact Nat.zero_le _
      · simp only [↓reduceIte]
        rw [← hLen]
        exact merkleMeasuredTargets_length L H xs _
  -- pointwise cover of the failure mass
  have hCover : ∀ H xs,
      QVec.queryMassOn (measuredMerkleFailure L lvl d opening H xs) (ψ H xs) ≤
        qsum d (fun k => QVec.queryMassOn (ev k H xs) (ψ H xs)) +
        (if freshCollision H xs = true then QVec.stateNormSq (ψ H xs) else 0) := by
    intro H xs
    have hColl : (if freshCollision H xs = true then QVec.stateNormSq (ψ H xs) else 0) =
        qsum cardX (fun o => if freshCollision H xs = true then
          QVec.queryWeight (ψ H xs) o else 0) := by
      cases freshCollision H xs
      · simp only [Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]
      · rfl
    have hSwap : qsum d (fun k => QVec.queryMassOn (ev k H xs) (ψ H xs)) =
        qsum cardX (fun o => qsum d (fun k =>
          if ev k H xs o = true then QVec.queryWeight (ψ H xs) o else 0)) :=
      qsum_comm d cardX (fun k o => if ev k H xs o = true then QVec.queryWeight (ψ H xs) o else 0)
    rw [hColl, hSwap, ← qsum_add]
    refine qsum_le_qsum (fun o => ?_)
    cases hF : measuredMerkleFailure L lvl d opening H xs o with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact Nat.zero_le _
    | true =>
      simp only [↓reduceIte]
      rcases measuredMerkleFailure_cover L lvl d hLvl opening H xs o hF with ⟨k, hk⟩ | hC
      · have hTerm := le_qsum_term
          (fun k => if ev k H xs o = true then QVec.queryWeight (ψ H xs) o else 0) k
        have hk' : ev k H xs o = true := hk
        simp only [hk', ↓reduceIte] at hTerm
        exact Nat.le_trans hTerm (Nat.le_add_right _ _)
      · rw [hC]
        exact Nat.le_add_left _ _
  have hSum : uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (measuredMerkleFailure L lvl d opening H xs) (ψ H xs))) ≤
      qsum d (fun k => uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (ev k H xs) (ψ H xs)))) +
      uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        if freshCollision H xs = true then QVec.stateNormSq (ψ H xs) else 0)) := by
    rw [← uniformOracleSum_qsum w cardX d (fun H k => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (ev k H xs) (ψ H xs))), ← uniformOracleSum_add]
    refine uniformOracleSum_le w cardX _ _ (fun H => ?_)
    rw [← sumLogs_qsum cardX Q d (fun xs k => QVec.queryMassOn (ev k H xs) (ψ H xs)),
      ← sumLogs_add]
    exact sumLogs_le_of_length cardX Q _ _ (fun xs _ => hCover H xs)
  have hLevels : 2 ^ w * qsum d (fun k => uniformOracleSum w cardX (fun H =>
        sumLogs cardX Q (fun xs => QVec.queryMassOn (ev k H xs) (ψ H xs)))) ≤
      d * ((3 * Q + 1) * Tot) := by
    rw [← qsum_mul_left, ← qsum_const d ((3 * Q + 1) * Tot)]
    exact qsum_le_qsum hLevel
  have hCollision := measured_record_collision_bound A Q (Nat.le_refl Q)
  have hAll := Nat.le_trans (Nat.mul_le_mul_left (2 ^ w) hSum)
    (by rw [Nat.mul_add]; exact Nat.add_le_add hLevels hCollision)
  refine Nat.le_trans hAll (Nat.le_of_eq ?_)
  show d * ((3 * Q + 1) * Tot) + triangleSum Q * Tot = (d * (3 * Q + 1) + triangleSum Q) * Tot
  rw [Nat.add_mul (d * (3 * Q + 1)) (triangleSum Q) Tot, Nat.mul_assoc d (3 * Q + 1) Tot]

/-! ## Size of the bound at deployment-scale parameters -/

theorem triangleSum_le_sq : ∀ t : Nat, triangleSum t ≤ t * t
  | 0 => Nat.le_refl 0
  | t + 1 => by
    have ih := triangleSum_le_sq t
    show triangleSum t + t ≤ (t + 1) * (t + 1)
    rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

/-- With 256-bit answers, up to `2^60` measured queries and paths of length up to 64, the
    failure fraction is below `2^-128`. -/
theorem measured_merkle_bound_below_128_bits (Q d : Nat) (hQ : Q ≤ 2 ^ 60) (hd : d ≤ 64) :
    (d * (3 * Q + 1) + triangleSum Q) * 2 ^ 128 < 2 ^ 256 := by
  have h1 : d * (3 * Q + 1) ≤ 64 * (3 * 2 ^ 60 + 1) :=
    Nat.mul_le_mul hd (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hQ) 1)
  have h2 : triangleSum Q ≤ 2 ^ 60 * 2 ^ 60 :=
    Nat.le_trans (triangleSum_le_sq Q) (Nat.mul_le_mul hQ hQ)
  have h3 : (d * (3 * Q + 1) + triangleSum Q) * 2 ^ 128 ≤
      (64 * (3 * 2 ^ 60 + 1) + 2 ^ 60 * 2 ^ 60) * 2 ^ 128 :=
    Nat.mul_le_mul_right _ (Nat.add_le_add h1 h2)
  exact Nat.lt_of_le_of_lt h3 (by decide)

#verify_constructive
  Qsag.merkleRecords_consistent
  Qsag.merkleRecords_reprogram_of_fresh
  Qsag.merklePathPoints_reprogram
  Qsag.merkle_measured_opening_classification
  Qsag.merkleFailurePoint_local
  Qsag.measuredMerkleFailure_cover
  Qsag.measured_merkle_extraction_failure_bound
  Qsag.measured_merkle_bound_below_128_bits

end Qsag
end

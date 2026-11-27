module
public import QsagWhirVerified.Proofs
public import Qsag.Oracle.Qrom
import all Qsag.Oracle.Qrom
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs

private theorem xor_zero_iff (x y : Nat) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (fun z => x ^^^ z) h
    simpa [← Nat.xor_assoc] using this.symm
  · rintro rfl
    exact Nat.xor_self _

private theorem sibling_iff_parent {x y : Nat} (hlt : x < y) :
    y = x ^^^ 1 ↔ x / 2 = y / 2 := by
  have hq : (x ^^^ 1) / 2 = x / 2 := by rw [Nat.xor_div_two]; simp
  have hne : x ^^^ 1 ≠ x := by
    intro h
    have bad := congrArg (fun z => x ^^^ z) h
    simp [← Nat.xor_assoc] at bad
  constructor
  · rintro rfl
    exact hq.symm
  · intro h
    omega

private theorem join_bit_parent {x y : Nat} (hne : x / 2 ≠ y / 2) :
    (x ^^^ y).log2 = (x / 2 ^^^ y / 2).log2 + 1 := by
  have hdiv := Nat.xor_div_two (a := x) (b := y)
  have hn := mt (xor_zero_iff _ _).mp hne
  rw [Nat.log2_def, ite_eq_left (by omega), hdiv]

private theorem parent_ge {nodes : List Nat} {lower : Nat} (h : ∀ x ∈ nodes, lower ≤ x / 2) :
    ∀ x ∈ (Qsag.steinerLevelStep nodes).1, lower ≤ x := by
  match nodes with
  | [] => simp [Qsag.steinerLevelStep]
  | [a] => simpa [Qsag.steinerLevelStep, Nat.shiftRight_eq_div_pow] using h a (by simp)
  | a :: b :: rest =>
    rw [Qsag.steinerLevelStep]
    split
    · simp only [List.mem_cons]
      rintro _ (rfl | hmem)
      · simpa [Nat.shiftRight_eq_div_pow] using h a (by simp)
      · exact parent_ge (nodes := rest) (fun x hx => h x (by simp [hx])) _ hmem
    · simp only [List.mem_cons]
      rintro _ (rfl | hmem)
      · simpa [Nat.shiftRight_eq_div_pow] using h a (by simp)
      · exact parent_ge (nodes := b :: rest) (fun x hx => h x (List.mem_cons_of_mem _ hx)) _ hmem
termination_by nodes.length

private theorem parent_head (a : Nat) (rest : List Nat) :
    ∃ tail, (Qsag.steinerLevelStep (a :: rest)).1 = a / 2 :: tail := by
  cases rest with
  | nil => exact ⟨[], by simp [Qsag.steinerLevelStep, Nat.shiftRight_eq_div_pow]⟩
  | cons b bs =>
    rw [Qsag.steinerLevelStep]; split <;>
      simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one] <;> exact ⟨_, rfl⟩

private theorem parents_sorted {nodes : List Nat} (hs : nodes.Pairwise (· < ·)) :
    (Qsag.steinerLevelStep nodes).1.Pairwise (· < ·) := by
  match nodes with
  | [] => simp [Qsag.steinerLevelStep]
  | [a] => simp [Qsag.steinerLevelStep]
  | a :: b :: rest =>
    obtain ⟨ha, hbs⟩ := List.pairwise_cons.mp hs
    have hab := ha b (by simp)
    obtain ⟨hb, hrest⟩ := List.pairwise_cons.mp hbs
    rw [Qsag.steinerLevelStep]
    split
    next he =>
      have hp := (sibling_iff_parent hab).mp he
      apply List.pairwise_cons.mpr
      refine ⟨?_, parents_sorted hrest⟩
      simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      exact parent_ge (lower := a / 2 + 1) (fun x hx => by have := hb x hx; omega)
    next he =>
      have hp := mt (sibling_iff_parent hab).mpr he
      apply List.pairwise_cons.mpr
      refine ⟨?_, parents_sorted hbs⟩
      simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      apply parent_ge (lower := a / 2 + 1)
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have := hb x hx; omega
termination_by nodes.length

private theorem prepend_cost (d x y : Nat) (rest : List Nat) (hxy : x < y)
    (hs : (y :: rest).Pairwise (· < ·)) (hroot : x / 2^d = y / 2^d) :
    Qsag.steinerCountLevels d (x :: y :: rest) + 1 =
      Qsag.steinerCountLevels d (y :: rest) + (x ^^^ y).log2 := by
  induction d generalizing x y rest with
  | zero => simp at hroot; omega
  | succ d ih =>
    simp only [Qsag.steinerCountLevels.eq_2]
    rw [Qsag.steinerLevelStep.eq_3]
    by_cases hpair : y = x ^^^ 1
    · have hp := (sibling_iff_parent hxy).mp hpair
      have hxor : x ^^^ y = 1 := by rw [hpair, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hy : Qsag.steinerLevelStep (y :: rest) =
          (y >>> 1 :: (Qsag.steinerLevelStep rest).1, (Qsag.steinerLevelStep rest).2 + 1) := by
        cases rest with
        | nil => rfl
        | cons z zs =>
          have hyz := (List.pairwise_cons.mp hs).1 z (by simp)
          have hn : z ≠ y ^^^ 1 := by rw [hpair, Nat.xor_assoc]; simp; omega
          rw [Qsag.steinerLevelStep.eq_3, ite_eq_right hn]
      simp only [ite_eq_left hpair, hy, Nat.shiftRight_eq_div_pow, Nat.pow_one, hp, hxor]
      have hz : Nat.log2 1 = 0 := rfl
      omega
    · have hd := mt (sibling_iff_parent hxy).mpr hpair
      obtain ⟨tail, ht⟩ := parent_head y rest
      have hs' := parents_sorted hs
      rw [ht] at hs'
      have hroot' : x / 2 / 2^d = y / 2 / 2^d := by
        rwa [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm 2, ← Nat.pow_succ]
      have hr := ih (x/2) (y/2) tail (by omega) hs' hroot'
      simp only [ite_eq_right hpair, ht, Nat.shiftRight_eq_div_pow, Nat.pow_one]
      rw [join_bit_parent hd]
      omega


private theorem level_cardinality (nodes : List Nat) :
    nodes.length + (Qsag.steinerLevelStep nodes).2 = 2 * (Qsag.steinerLevelStep nodes).1.length := by
  match nodes with
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest =>
    rw [Qsag.steinerLevelStep.eq_3]
    split
    · have h := level_cardinality rest
      simp only [List.length_cons]; omega
    · have h := level_cardinality (b :: rest)
      simp only [List.length_cons] at h ⊢; omega
termination_by nodes.length

private theorem missing_leaf_cost (d : Nat) (nodes : List Nat) (ne : nodes ≠ [])
    (short : nodes.length < 2^d) : 0 < Qsag.steinerCountLevels d nodes := by
  induction d generalizing nodes with
  | zero => cases nodes <;> simp_all
  | succ d ih =>
    have hcard := level_cardinality nodes
    rw [Qsag.steinerCountLevels.eq_2]
    by_cases hh : (Qsag.steinerLevelStep nodes).2 = 0
    · have hn : (Qsag.steinerLevelStep nodes).1 ≠ [] := by
        cases nodes with
        | nil => contradiction
        | cons a bs => obtain ⟨xs, hx⟩ := parent_head a bs; rw [hx]; simp
      have h := ih _ hn (by rw [Nat.pow_succ] at short; omega)
      omega
    · omega

private theorem sorted_length (lo hi : Nat) (xs : List Nat) (bounds : lo ≤ hi)
    (h : ∀ x ∈ xs, lo ≤ x ∧ x < hi) (hs : xs.Pairwise (· < ·)) : lo + xs.length ≤ hi := by
  induction xs generalizing lo with
  | nil => simpa using bounds
  | cons x xs ih =>
    have hx := h x (by simp)
    obtain ⟨hxall, hrest⟩ := List.pairwise_cons.mp hs
    have hr := ih (x+1) (by omega) (fun z hz => ⟨hxall z hz, (h z (by simp [hz])).2⟩) hrest
    simp only [List.length_cons]; omega

private theorem heap_join (d x y : Nat) (hx : x < 2^d) (hy : y < 2^d) :
    ((2^d+x) ^^^ (2^d+y)) = x ^^^ y := by
  have hv : 0 < 2^d := Nat.two_pow_pos _
  have hqx : (2^d+x) / 2^d = 1 := by rw [Nat.add_div_left _ hv, Nat.div_eq_of_lt hx]
  have hqy : (2^d+y) / 2^d = 1 := by rw [Nat.add_div_left _ hv, Nat.div_eq_of_lt hy]
  have hdiv := Nat.xor_div_two_pow (a := 2^d+x) (b := 2^d+y) (n := d)
  rw [hqx, hqy, Nat.xor_self] at hdiv
  have hmod := Nat.xor_mod_two_pow (a := 2^d+x) (b := 2^d+y) (n := d)
  rw [Nat.add_mod_left, Nat.add_mod_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod
  have he := Nat.mod_add_div ((2^d+x) ^^^ (2^d+y)) (2^d)
  rw [hdiv, Nat.mul_zero, Nat.add_zero] at he
  exact he.symm.trans hmod

private theorem prepend_siblings (d x y : Nat) (rest : List Nat) (hx : x < y)
    (hy : y < 2^d) (hs : (y :: rest).Pairwise (· < ·)) :
    Qsag.steinerSiblingCount d (x :: y :: rest) + 1 =
      Qsag.steinerSiblingCount d (y :: rest) + (x ^^^ y).log2 := by
  let base := 2^d
  have hpos : 0 < base := Nat.two_pow_pos _
  have hr (z : Nat) (hz : z < base) : (base + z)/2^d = 1 := by
    rw [Nat.add_div_left _ hpos, Nat.div_eq_of_lt hz]
  have h := prepend_cost d (base+x) (base+y) (rest.map (base+·)) (by omega)
    (by simpa using hs.map (base+·) (fun _ _ h => Nat.add_lt_add_left h base))
    ((hr x (by change x < 2^d; omega)).trans (hr y hy).symm)
  rw [heap_join d x y (by omega) hy] at h
  exact h

private theorem single_cost (d x : Nat) : Qsag.steinerCountLevels d [x] = d := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih =>
    rw [Qsag.steinerCountLevels.eq_2, Qsag.steinerLevelStep.eq_2]
    simp [ih, Nat.add_comm]

private theorem append_siblings (d : Nat) (pref : List Nat) (x y : Nat)
    (hxy : x < y) (hy : y < 2^d) (hs : (pref ++ [x]).Pairwise (· < ·)) :
    Qsag.steinerSiblingCount d (pref ++ [x,y]) + 1 =
      Qsag.steinerSiblingCount d (pref ++ [x]) + (x ^^^ y).log2 := by
  induction pref with
  | nil =>
    have hc := prepend_siblings d x y [] hxy hy (by simp)
    simpa [Qsag.steinerSiblingCount.eq_1, single_cost] using hc
  | cons a pref ih =>
    obtain ⟨ha, htail⟩ := List.pairwise_cons.mp hs
    have hi := ih htail
    have hx := ha x (by simp)
    have hs' : (pref ++ [x,y]).Pairwise (· < ·) := by
      rw [show pref ++ [x,y] = (pref ++ [x]) ++ [y] by simp, List.pairwise_append]
      refine ⟨htail, by simp, ?_⟩
      intro z hz w hw
      have : w = y := by simpa using hw
      subst w
      rcases List.mem_append.mp hz with hz | hz
      · have h := (List.pairwise_append.mp htail).2.2 _ hz x (by simp); omega
      · have he : z = x := by simpa using hz
        exact he ▸ hxy
    cases pref with
    | nil =>
      have h1 := prepend_siblings d a x [y] hx (by omega) hs'
      have h2 := prepend_siblings d a x [] hx (by omega) htail
      simp only [List.nil_append, List.cons_append] at hi ⊢
      omega
    | cons b bs =>
      have hab := ha b (by simp)
      have hbx := (List.pairwise_cons.mp htail).1 x (by simp)
      have h1 := prepend_siblings d a b (bs ++ [x,y]) hab (by omega) hs'
      have h2 := prepend_siblings d a b (bs ++ [x]) hab (by omega) htail
      simp only [List.cons_append] at hi ⊢
      omega


private theorem canopy_order (limit x : Nat) (xs : List Nat) :
    Qsag.canopyIndicesOk limit (x :: xs) = true ↔
      (x :: xs).Pairwise (· < ·) ∧ ∀ z ∈ x :: xs, z < limit := by
  induction xs generalizing x with
  | nil => simp [Qsag.canopyIndicesOk.eq_2]
  | cons y ys ih =>
    rw [Qsag.canopyIndicesOk.eq_3, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hxy, hsort, hbound⟩
      have hy := hbound y (by simp)
      refine ⟨List.pairwise_cons.mpr ⟨?_, hsort⟩, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hxy
        · exact Nat.lt_trans hxy ((List.pairwise_cons.mp hsort).1 _ hz)
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · omega
        · exact hbound _ hz
    · rintro ⟨hs, hb⟩
      obtain ⟨hxy, hy⟩ := List.pairwise_cons.mp hs
      exact ⟨hxy _ (by simp), hy, fun z hz => hb _ (List.mem_cons_of_mem _ hz)⟩

private theorem suffix_sorted_of_ok (limit x count : Nat) (xs : List Usize) (hx : x < limit)
    (hok : (steinerSuffix limit x count xs).2 = true) :
    Qsag.canopyIndicesOk limit (x :: xs.map UScalar.val) = true := by
  induction xs generalizing x count with
  | nil => simp [Qsag.canopyIndicesOk.eq_2, hx]
  | cons y ys ih =>
    rw [steinerSuffix] at hok
    split at hok
    next h =>
      simp only [List.map_cons, Qsag.canopyIndicesOk.eq_3, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, ih _ _ h.2.1 hok⟩
    next => contradiction

private theorem suffix_canonical (d : Nat) (xs : List Usize) (pref : List Nat) (prev : Nat)
    (hs : (pref ++ prev :: xs.map UScalar.val).Pairwise (· < ·))
    (bound : ∀ z ∈ pref ++ prev :: xs.map UScalar.val, z < 2^d) :
    steinerSuffix (2^d) prev (Qsag.steinerSiblingCount d (pref ++ [prev])) xs =
      (Qsag.steinerSiblingCount d (pref ++ prev :: xs.map UScalar.val), true) := by
  induction xs generalizing pref prev with
  | nil => rfl
  | cons leaf rest ih =>
    let xs := rest.map UScalar.val
    have hs' : ((pref ++ [prev]) ++ leaf.val :: xs).Pairwise (· < ·) := by
      simpa [List.append_assoc, xs] using hs
    obtain ⟨hpre, _, hcross⟩ := List.pairwise_append.mp hs'
    have hlt (z : Nat) (hz : z ∈ pref ++ [prev]) : z < leaf.val := hcross z hz _ (by simp)
    have hp := hlt prev (by simp)
    have hl := bound leaf.val (by simp)
    have hlen := sorted_length 0 leaf.val (pref ++ [prev]) (Nat.zero_le _)
      (fun z hz => ⟨Nat.zero_le _, hlt z hz⟩) hpre
    have hpos : 0 < Qsag.steinerSiblingCount d (pref ++ [prev]) := by
      rw [Qsag.steinerSiblingCount.eq_1]
      apply missing_leaf_cost
      · simp
      · rw [List.length_map]; omega
    have hadd := append_siblings d pref prev leaf.val hp hl hpre
    have he : Qsag.steinerSiblingCount d (pref ++ [prev]) - 1 + (prev ^^^ leaf.val).log2 =
        Qsag.steinerSiblingCount d ((pref ++ [prev]) ++ [leaf.val]) := by
      rw [List.append_assoc]; simp only [List.cons_append, List.nil_append]; omega
    rw [steinerSuffix, ite_eq_left ⟨hp, hl, hpos⟩, he]
    have h := ih (pref ++ [prev]) leaf.val hs'
      (by simpa [List.append_assoc, xs] using bound)
    simpa [List.append_assoc] using h

theorem compute_steiner_multiproof_siblings_refines_qsag (depth : U32) (indices : Slice Usize) :
    compute_steiner_multiproof_siblings depth indices =
      .ok (if depth.val ≤ 28 ∧ Qsag.canopyIndicesOk (2^depth.val) (indices.val.map UScalar.val) then
        some (UScalar.ofNat .Usize (Qsag.steinerSiblingCount depth.val (indices.val.map UScalar.val)))
        else none) := by
  rw [compute_steiner_multiproof_siblings_spec]
  cases he : indices.val with
  | nil => simp [steinerCount, Qsag.canopyIndicesOk.eq_1]
  | cons x xs =>
    by_cases hd : depth.val ≤ 28
    · have hd' : ¬ depth.val > 28 := by omega
      by_cases hok : Qsag.canopyIndicesOk (2^depth.val) (x.val :: xs.map UScalar.val) = true
      · obtain ⟨hs, hb⟩ := (canopy_order _ _ _).mp hok
        have hx := hb x.val (by simp)
        have hv := suffix_canonical depth.val xs [] x.val hs hb
        have hfirst : Qsag.steinerSiblingCount depth.val [x.val] = depth.val := by
          simp [Qsag.steinerSiblingCount.eq_1, single_cost]
        simp only [List.nil_append, hfirst] at hv
        simp [steinerCount, hd, hd', hok, Nat.not_le_of_lt hx, hv]
      · by_cases hx : x.val < 2^depth.val
        · have hb := mt (suffix_sorted_of_ok (2^depth.val) x.val depth.val xs hx) hok
          simp [steinerCount, hd, hd', hok, Nat.not_le_of_lt hx, hb]
        · simp [steinerCount, hd, hd', hok, Nat.le_of_not_gt hx]
    · have hg : depth.val > 28 := by omega
      simp [steinerCount, hg, hd]


private theorem parents_length_le (nodes : List Nat) : (Qsag.steinerLevelStep nodes).1.length ≤ nodes.length := by
  match nodes with
  | [] => decide
  | [a] => simp [Qsag.steinerLevelStep]
  | a :: b :: rest =>
    rw [Qsag.steinerLevelStep.eq_3]
    split
    · have := parents_length_le rest
      simp only [List.length_cons]; omega
    · have := parents_length_le (b :: rest)
      simp only [List.length_cons] at *; omega
termination_by nodes.length

private theorem levels_count_le (d : Nat) (nodes : List Nat) :
    Qsag.steinerCountLevels d nodes ≤ d * nodes.length := by
  induction d generalizing nodes with
  | zero => simp [Qsag.steinerCountLevels.eq_1]
  | succ d ih =>
    rw [Qsag.steinerCountLevels.eq_2, Nat.succ_mul]
    have hp := parents_length_le nodes
    have hc := level_cardinality nodes
    have hi := Nat.le_trans (ih _) (Nat.mul_le_mul_left d hp)
    omega

theorem steiner_count_fits_usize (d : Nat) (xs : List Nat) (hd : d ≤ 28)
    (hok : Qsag.canopyIndicesOk (2^d) xs = true) : Qsag.steinerSiblingCount d xs < 2^64 := by
  cases xs with
  | nil => simp [Qsag.canopyIndicesOk.eq_1] at hok
  | cons x xs =>
    obtain ⟨hs, hb⟩ := (canopy_order _ _ _).mp hok
    have hlen := sorted_length 0 (2^d) (x::xs) (Nat.zero_le _) (fun y hy => ⟨Nat.zero_le _, hb y hy⟩) hs
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) hd
    rw [Qsag.steinerSiblingCount.eq_1]
    apply Nat.lt_of_le_of_lt (levels_count_le _ _)
    rw [List.length_map]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hd (Nat.le_trans (by simpa using hlen) hp)) (by decide)

theorem sibling_path_below_join_canopy (d : Nat) (x y : U64) (hxy : x.val < y.val)
    (hy : y.val < 2^d) :
    ∃ h, sibling_path_below_join (x ^^^ y) = .ok h ∧
      Qsag.steinerSiblingCount d [x.val, y.val] + 1 = d + h.val := by
  rw [sibling_path_below_join_spec]
  refine ⟨_, rfl, ?_⟩
  have hlt := Nat.lt_of_le_of_lt (Nat.log2_le_self (x ^^^ y : U64).val) (UScalar.val_lt (x ^^^ y))
  rw [UScalar.val_ofNat, Nat.mod_eq_of_lt hlt]
  have hv : (x ^^^ y : U64).val = x.val ^^^ y.val := by
    change (x ^^^ y : U64).bv.toNat = _
    rw [UScalar.bv_xor, BitVec.toNat_xor]
  rw [hv]
  have h := prepend_siblings d x.val y.val [] hxy hy (by simp)
  have hs : Qsag.steinerSiblingCount d [y.val] = d := by
    simp [Qsag.steinerSiblingCount.eq_1, single_cost]
  simpa only [hs] using h

end qsag_whir_verified.proofs
end

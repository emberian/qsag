module
/- Finite committee masks, constructive quorum enumeration and disjoint leaf ranges. -/
public import Qsag.Tactic.Prelude
public section
namespace Qsag
set_option autoImplicit false
/-! ## §0. Constructive `0-Classical` Finite Bitmask Calculus & Pigeonhole Extractors -/

/-- Constructive bitmask subset of `Fin n` (`0 Classical.choice`). -/
structure CustodiansMask (n : Nat) where
  mem : Fin n → Bool

/-- Recursive head-prepending constructor on `CustodiansMask`. -/
@[expose] def consMask (b : Bool) {n : Nat} (m : CustodiansMask n) : CustodiansMask (n + 1) where
  mem i :=
    match i with
    | ⟨0, _⟩ => b
    | ⟨k + 1, hk⟩ => m.mem ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Tail projection dropping index `0` from `CustodiansMask (n + 1)`. -/
@[expose] def tailMask {n : Nat} (m : CustodiansMask (n + 1)) : CustodiansMask n where
  mem i := m.mem ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

theorem consMask_head_tail {n : Nat} (m : CustodiansMask (n + 1)) :
    consMask (m.mem ⟨0, Nat.zero_lt_succ n⟩) (tailMask m) = m := by
  cases m with
  | mk f =>
    apply congrArg CustodiansMask.mk
    funext i
    cases i with
    | mk val isLt =>
      cases val <;> rfl

theorem consMask_inj {n : Nat} {b₁ b₂ : Bool} {m₁ m₂ : CustodiansMask n}
    (h : consMask b₁ m₁ = consMask b₂ m₂) : b₁ = b₂ ∧ m₁ = m₂ := by
  have hb : b₁ = b₂ := congrArg (fun x => x.mem ⟨0, Nat.zero_lt_succ n⟩) h
  have hm : m₁ = m₂ := by
    cases m₁ with
    | mk f₁ =>
      cases m₂ with
      | mk f₂ =>
        apply congrArg CustodiansMask.mk
        funext i
        exact congrArg (fun x => x.mem ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) h
  exact ⟨hb, hm⟩

@[expose] def maskEqDec : {n : Nat} → CustodiansMask n → CustodiansMask n → Bool
  | 0, _, _ => true
  | n + 1, a, b =>
    (a.mem ⟨0, Nat.zero_lt_succ n⟩ == b.mem ⟨0, Nat.zero_lt_succ n⟩) &&
      maskEqDec (tailMask a) (tailMask b)

theorem maskEqDec_iff_eq :
    ∀ {n : Nat} (a b : CustodiansMask n), maskEqDec a b = true ↔ a = b
  | 0, ⟨f⟩, ⟨g⟩ => by
    simp only [maskEqDec, true_iff]
    apply congrArg CustodiansMask.mk
    funext i
    exact Fin.elim0 i
  | n + 1, a, b => by
    simp only [maskEqDec, Bool.and_eq_true, beq_iff_eq, maskEqDec_iff_eq (tailMask a) (tailMask b)]
    constructor
    · rintro ⟨h0, hTail⟩
      rw [← consMask_head_tail a, ← consMask_head_tail b, h0, hTail]
    · rintro rfl
      exact ⟨rfl, rfl⟩

/-- Constructive `DecidableEq` on `CustodiansMask n` using zero `Classical.choice`. -/
instance constructiveCustodiansMaskDecidableEq (n : Nat) : DecidableEq (CustodiansMask n) :=
  fun a b =>
    if h : maskEqDec a b = true then
      .isTrue ((maskEqDec_iff_eq a b).mp h)
    else
      .isFalse (fun hEq => h ((maskEqDec_iff_eq a b).mpr hEq))

/-- Exact cardinality of a finite custodian bitmask. -/
@[expose] def maskCard : {n : Nat} → CustodiansMask n → Nat
  | 0, _ => 0
  | n + 1, S => (if S.mem ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) + maskCard (tailMask S)

/-- Intersection `A ∩ B` of two custodian bitmasks. -/
@[expose] def maskInter {n : Nat} (A B : CustodiansMask n) : CustodiansMask n where
  mem i := A.mem i && B.mem i

/-- Set difference `A \ B` of two custodian bitmasks. -/
@[expose] def maskDiff {n : Nat} (A B : CustodiansMask n) : CustodiansMask n where
  mem i := A.mem i && !B.mem i

/-- Subset predicate `A ⊆ B` on custodian bitmasks. -/
@[expose] def maskSub {n : Nat} (A B : CustodiansMask n) : Prop :=
  ∀ i : Fin n, A.mem i = true → B.mem i = true

@[expose] def emptyMask (n : Nat) : CustodiansMask n := ⟨fun _ => false⟩

@[simp] theorem maskCard_zero (S : CustodiansMask 0) : maskCard S = 0 := rfl

@[simp] theorem maskCard_succ {n : Nat} (S : CustodiansMask (n + 1)) :
    maskCard S = (if S.mem ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) + maskCard (tailMask S) := rfl

@[simp] theorem tailMask_consMask {n : Nat} (b : Bool) (m : CustodiansMask n) :
    tailMask (consMask b m) = m := by
  cases m; rfl

@[simp] theorem maskCard_consMask {n : Nat} (b : Bool) (m : CustodiansMask n) :
    maskCard (consMask b m) = (if b then 1 else 0) + maskCard m := by
  simp only [maskCard_succ, tailMask_consMask]
  rfl

theorem maskCard_empty (n : Nat) : maskCard (emptyMask n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [maskCard_succ, emptyMask, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact ih

theorem maskCard_le_n : ∀ {n : Nat} (S : CustodiansMask n), maskCard S ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, S => by
    simp only [maskCard_succ]
    have ih := maskCard_le_n (tailMask S)
    cases S.mem ⟨0, Nat.zero_lt_succ n⟩ <;> simp <;> omega

theorem maskCard_mono : ∀ {n : Nat} {A B : CustodiansMask n},
    maskSub A B → maskCard A ≤ maskCard B
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, A, B, hSub => by
    simp only [maskCard_succ]
    have hTail : maskSub (tailMask A) (tailMask B) :=
      fun i hi => hSub ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ hi
    have ih := maskCard_mono hTail
    have h0 := hSub ⟨0, Nat.zero_lt_succ n⟩
    cases ha : A.mem ⟨0, Nat.zero_lt_succ n⟩
    · cases B.mem ⟨0, Nat.zero_lt_succ n⟩ <;> simp <;> omega
    · rw [h0 ha]
      simp only [↓reduceIte]
      omega

theorem maskCard_union_inter : ∀ {n : Nat} (A B : CustodiansMask n),
    maskCard ⟨fun i => A.mem i || B.mem i⟩ + maskCard (maskInter A B) =
      maskCard A + maskCard B
  | 0, _, _ => rfl
  | n + 1, A, B => by
    simp only [maskCard_succ]
    have ih := maskCard_union_inter (tailMask A) (tailMask B)
    have hU : tailMask ⟨fun i => A.mem i || B.mem i⟩ =
        ⟨fun i => (tailMask A).mem i || (tailMask B).mem i⟩ := rfl
    have hI : tailMask (maskInter A B) = maskInter (tailMask A) (tailMask B) := rfl
    have hInter0 : (maskInter A B).mem ⟨0, Nat.zero_lt_succ n⟩ =
        (A.mem ⟨0, Nat.zero_lt_succ n⟩ && B.mem ⟨0, Nat.zero_lt_succ n⟩) := rfl
    rw [hU, hI, hInter0]
    by_cases ha : A.mem ⟨0, Nat.zero_lt_succ n⟩ = true <;>
      by_cases hb : B.mem ⟨0, Nat.zero_lt_succ n⟩ = true
    · simp only [ha, hb, Bool.or_self, Bool.and_self, ↓reduceIte]; omega
    · have hbf : B.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp hb
      simp only [ha, hbf, Bool.true_or, Bool.true_and, Bool.false_eq_true, ↓reduceIte]; omega
    · have haf : A.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp ha
      simp only [haf, hb, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; omega
    · have haf : A.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp ha
      have hbf : B.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp hb
      simp only [haf, hbf, Bool.or_self, Bool.and_self, Bool.false_eq_true, ↓reduceIte]; omega

/-- Constructive inclusion-exclusion lower bound: `|A| + |B| ≤ n + |A ∩ B|`. -/
theorem maskCard_inter_add_n_ge {n : Nat} (A B : CustodiansMask n) :
    maskCard A + maskCard B ≤ n + maskCard (maskInter A B) := by
  have hUI := maskCard_union_inter A B
  have hLe := maskCard_le_n ⟨fun i => A.mem i || B.mem i⟩
  omega

theorem maskCard_diff_add_inter : ∀ {n : Nat} (A B : CustodiansMask n),
    maskCard (maskDiff A B) + maskCard (maskInter A B) = maskCard A
  | 0, _, _ => rfl
  | n + 1, A, B => by
    simp only [maskCard_succ]
    have ih := maskCard_diff_add_inter (tailMask A) (tailMask B)
    have hD : tailMask (maskDiff A B) = maskDiff (tailMask A) (tailMask B) := rfl
    have hI : tailMask (maskInter A B) = maskInter (tailMask A) (tailMask B) := rfl
    have hDiff0 : (maskDiff A B).mem ⟨0, Nat.zero_lt_succ n⟩ =
        (A.mem ⟨0, Nat.zero_lt_succ n⟩ && !B.mem ⟨0, Nat.zero_lt_succ n⟩) := rfl
    have hInter0 : (maskInter A B).mem ⟨0, Nat.zero_lt_succ n⟩ =
        (A.mem ⟨0, Nat.zero_lt_succ n⟩ && B.mem ⟨0, Nat.zero_lt_succ n⟩) := rfl
    rw [hD, hI, hDiff0, hInter0]
    by_cases ha : A.mem ⟨0, Nat.zero_lt_succ n⟩ = true <;>
      by_cases hb : B.mem ⟨0, Nat.zero_lt_succ n⟩ = true
    · simp only [ha, hb, Bool.not_true, Bool.and_false, Bool.and_self, Bool.false_eq_true, ↓reduceIte]; omega
    · have hbf : B.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp hb
      simp only [ha, hbf, Bool.not_false, Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]; omega
    · have haf : A.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp ha
      simp only [haf, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; omega
    · have haf : A.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp ha
      have hbf : B.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp hb
      simp only [haf, hbf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; omega

theorem maskCard_diff_ge {n : Nat} (A B : CustodiansMask n) :
    maskCard A ≤ maskCard (maskDiff A B) + maskCard B := by
  have hSplit := maskCard_diff_add_inter A B
  have hSub : maskSub (maskInter A B) B := by
    intro i hi
    simp only [maskInter, Bool.and_eq_true] at hi
    exact hi.2
  have hMono := maskCard_mono hSub
  omega

theorem maskCard_singleton : ∀ {n : Nat} (target : Fin n),
    maskCard ⟨fun j => decide (j = target)⟩ = 1
  | 0, target => Fin.elim0 target
  | n + 1, ⟨0, _⟩ => by
    simp only [maskCard_succ, decide_true, ↓reduceIte]
    have hTailEmpty : tailMask ⟨fun j : Fin (n + 1) => decide (j = ⟨0, Nat.zero_lt_succ n⟩)⟩ =
        emptyMask n := by
      apply congrArg CustodiansMask.mk
      funext j
      dsimp only [tailMask, emptyMask]
      simp only [decide_eq_false_iff_not]
      intro hEq
      cases congrArg Fin.val hEq
    rw [hTailEmpty, maskCard_empty]
  | n + 1, ⟨k + 1, hk⟩ => by
    have h0Ne : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ :=
      fun hEq => by cases congrArg Fin.val hEq
    simp only [maskCard_succ, decide_eq_false h0Ne, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    have hTailShift :
        tailMask ⟨fun j : Fin (n + 1) => decide (j = ⟨k + 1, hk⟩)⟩ =
        ⟨fun j : Fin n => decide (j = ⟨k, Nat.lt_of_succ_lt_succ hk⟩)⟩ := by
      apply congrArg CustodiansMask.mk
      funext j
      dsimp only [tailMask]
      by_cases hjk : j.val = k
      · have h2 : j = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := Fin.ext hjk
        subst h2
        simp
      · have h1 : (⟨j.val + 1, Nat.succ_lt_succ j.2⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ :=
          fun he => hjk (Nat.succ.inj (congrArg Fin.val he))
        have h2 : j ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ :=
          fun he => hjk (congrArg Fin.val he)
        simp [h1, h2]
    rw [hTailShift]
    exact maskCard_singleton ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Constructive executable witness extractor: given `0 < maskCard S`, computes the smallest-index
    custodian `p : Fin n` with `S.mem p = true` using **zero `Classical.choice`**. -/
def extractMaskMember : {n : Nat} → (S : CustodiansMask n) → 0 < maskCard S →
    { p : Fin n // S.mem p = true }
  | 0, _, hPos => False.elim (Nat.lt_irrefl 0 hPos)
  | n + 1, S, hPos =>
    if h0 : S.mem ⟨0, Nat.zero_lt_succ n⟩ = true then
      ⟨⟨0, Nat.zero_lt_succ n⟩, h0⟩
    else
      have h0f : S.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.eq_false_iff.mpr h0
      have hTailPos : 0 < maskCard (tailMask S) := by
        simp only [maskCard_succ, h0f, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hPos
        exact hPos
      let ⟨pTail, hpTail⟩ := extractMaskMember (tailMask S) hTailPos
      ⟨⟨pTail.1 + 1, Nat.succ_lt_succ pTail.2⟩, hpTail⟩

/-- Constructive BFT Quorum-Intersection Honest Custodian Extractor (`0 Classical.choice`):
    Whenever `2 * q > n + f`, `|Q1| ≥ q`, `|Q2| ≥ q`, and `|Corrupt| ≤ f`, computes an explicit
    honest custodian `p : Fin n` in `(Q1 ∩ Q2) \ Corrupt`. -/
def extractBeltHonestQuorumWitness {n q f : Nat}
    (Q1 Q2 Corrupt : CustodiansMask n)
    (hQuorum : 2 * q > n + f)
    (hQ1 : q ≤ maskCard Q1)
    (hQ2 : q ≤ maskCard Q2)
    (hCorrupt : maskCard Corrupt ≤ f) :
    { p : Fin n // Q1.mem p = true ∧ Q2.mem p = true ∧ Corrupt.mem p = false } :=
  have hInterLb : f + 1 ≤ maskCard (maskInter Q1 Q2) := by
    have hIE := maskCard_inter_add_n_ge Q1 Q2
    omega
  have hHonestPos : 0 < maskCard (maskDiff (maskInter Q1 Q2) Corrupt) := by
    have hDiff := maskCard_diff_ge (maskInter Q1 Q2) Corrupt
    omega
  let ⟨p, hp⟩ := extractMaskMember (maskDiff (maskInter Q1 Q2) Corrupt) hHonestPos
  ⟨p, by
    simp only [maskDiff, maskInter, Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩⟩

theorem committeeMasks_nodup_map_inj {α β : Type} {f : α → β}
    (hf : ∀ x y, f x = f y → x = y) : ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => .nil
  | a :: l, h => by
    obtain ⟨hNotMem, hTail⟩ := List.nodup_cons.mp h
    refine List.Pairwise.cons ?_ (committeeMasks_nodup_map_inj hf hTail)
    intro y hy hEq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hax := hf a x hEq
    subst hax
    exact hNotMem hx

/-- Constructive enumeration of all `t`-custodian subcommittees of `Fin n` (`0 Classical.choice`). -/
@[expose] def chooseMasks : (n t : Nat) → List (CustodiansMask n)
  | 0, 0 => [⟨fun i => Fin.elim0 i⟩]
  | 0, _ + 1 => []
  | n + 1, 0 => (chooseMasks n 0).map (consMask false)
  | n + 1, t + 1 =>
    (chooseMasks n t).map (consMask true) ++ (chooseMasks n (t + 1)).map (consMask false)

theorem chooseMasks_card :
    ∀ (n t : Nat) {Q : CustodiansMask n}, Q ∈ chooseMasks n t → maskCard Q = t
  | 0, 0, _, _ => rfl
  | 0, _ + 1, _, h => by cases h
  | n + 1, 0, Q, h => by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
    rw [maskCard_consMask, chooseMasks_card n 0 hm]
    rfl
  | n + 1, t + 1, Q, h => by
    rcases List.mem_append.mp h with hT | hF
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hT
      rw [maskCard_consMask, chooseMasks_card n t hm]
      simp [Nat.add_comm]
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hF
      rw [maskCard_consMask, chooseMasks_card n (t + 1) hm]
      simp

theorem mem_chooseMasks_of_card :
    ∀ (n : Nat) (Q : CustodiansMask n), Q ∈ chooseMasks n (maskCard Q)
  | 0, Q => by
    simp only [maskCard_zero, chooseMasks, List.mem_singleton]
    apply congrArg CustodiansMask.mk
    funext i; exact Fin.elim0 i
  | n + 1, Q => by
    have ih := mem_chooseMasks_of_card n (tailMask Q)
    have hEta := consMask_head_tail Q
    cases h0 : Q.mem ⟨0, Nat.zero_lt_succ n⟩
    · rw [h0] at hEta
      have hCardEq : maskCard Q = maskCard (tailMask Q) := by
        rw [maskCard_succ, h0]; simp
      cases htc : maskCard (tailMask Q) with
      | zero =>
        rw [htc] at ih hCardEq
        rw [hCardEq, ← hEta]
        exact List.mem_map.mpr ⟨tailMask Q, ih, rfl⟩
      | succ k =>
        rw [htc] at ih hCardEq
        rw [hCardEq, ← hEta]
        exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨tailMask Q, ih, rfl⟩))
    · rw [h0] at hEta
      have hCardEq : maskCard Q = maskCard (tailMask Q) + 1 := by
        rw [maskCard_succ, h0]
        simp [Nat.add_comm]
      rw [hCardEq, ← hEta]
      exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨tailMask Q, ih, rfl⟩))

theorem chooseMasks_nodup : ∀ (n t : Nat), (chooseMasks n t).Nodup
  | 0, 0 => List.Pairwise.cons (fun _ h => by cases h) .nil
  | 0, _ + 1 => .nil
  | n + 1, 0 =>
    committeeMasks_nodup_map_inj (fun _ _ h => (consMask_inj h).2) (chooseMasks_nodup n 0)
  | n + 1, t + 1 => by
    rw [chooseMasks, List.nodup_append]
    refine ⟨committeeMasks_nodup_map_inj (fun _ _ h => (consMask_inj h).2) (chooseMasks_nodup n t),
            committeeMasks_nodup_map_inj (fun _ _ h => (consMask_inj h).2) (chooseMasks_nodup n (t + 1)), ?_⟩
    intro a ha b hb hEq
    obtain ⟨ma, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨mb, _, rfl⟩ := List.mem_map.mp hb
    have hbEq := (consMask_inj hEq).1
    cases hbEq

/-- Deployed committee counts: `(2, 3)` yields `3` subtrees; `(3, 5)` yields `10` subtrees. -/
theorem chooseMasks_deployed_counts :
    (chooseMasks 3 2).length = 3 ∧ (chooseMasks 5 3).length = 10 := by
  decide

/-- Constructive subcommittee selector (`0 Classical.choice`): given `t ≤ maskCard avail`,
    computes an explicit `t`-member committee `Q ⊆ avail`. -/
def selectSubcommittee : {n : Nat} → (t : Nat) → (avail : CustodiansMask n) →
    t ≤ maskCard avail →
    { Q : CustodiansMask n // maskCard Q = t ∧ maskSub Q avail }
  | n, 0, _, _ => ⟨emptyMask n, maskCard_empty n, fun _ h => by cases h⟩
  | 0, _ + 1, _, hLe => False.elim (by simp [maskCard_zero] at hLe)
  | n + 1, t + 1, avail, hLe =>
    if h0 : avail.mem ⟨0, Nat.zero_lt_succ n⟩ = true then
      have hTailLe : t ≤ maskCard (tailMask avail) := by
        simp only [maskCard_succ, h0, ↓reduceIte] at hLe
        omega
      let ⟨Qt, hCardQt, hSubQt⟩ := selectSubcommittee t (tailMask avail) hTailLe
      ⟨consMask true Qt,
       by rw [maskCard_consMask, hCardQt]; simp [Nat.add_comm],
       by
         intro i hi
         cases i with
         | mk val isLt =>
           cases val with
           | zero => exact h0
           | succ k => exact hSubQt ⟨k, Nat.lt_of_succ_lt_succ isLt⟩ hi⟩
    else
      have h0f : avail.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp h0
      have hTailLe : t + 1 ≤ maskCard (tailMask avail) := by
        simp only [maskCard_succ, h0f, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hLe
        exact hLe
      let ⟨Qt, hCardQt, hSubQt⟩ := selectSubcommittee (t + 1) (tailMask avail) hTailLe
      ⟨consMask false Qt,
       by rw [maskCard_consMask, hCardQt]; simp,
       by
         intro i hi
         cases i with
         | mk val isLt =>
           cases val with
           | zero => cases hi
           | succ k => exact hSubQt ⟨k, Nat.lt_of_succ_lt_succ isLt⟩ hi⟩

/-- Global Merkle leaf index assigned to `(committeeIdx, localEpoch)` under disjoint partitioning. -/
@[expose] def committeeGlobalLeaf (leavesPerCommittee committeeIdx localEpoch : Nat) : Nat :=
  committeeIdx * leavesPerCommittee + localEpoch

theorem committee_leaf_ranges_disjoint {leavesPerCommittee c₁ c₂ e₁ e₂ : Nat}
    (he₁ : e₁ < leavesPerCommittee) (he₂ : e₂ < leavesPerCommittee)
    (hEq : committeeGlobalLeaf leavesPerCommittee c₁ e₁ =
           committeeGlobalLeaf leavesPerCommittee c₂ e₂) :
    c₁ = c₂ ∧ e₁ = e₂ := by
  unfold committeeGlobalLeaf at hEq
  have hc : c₁ = c₂ := by
    by_cases hlt : c₁ < c₂
    · have hMul : (c₁ + 1) * leavesPerCommittee ≤ c₂ * leavesPerCommittee :=
        Nat.mul_le_mul_right leavesPerCommittee hlt
      rw [Nat.add_mul, Nat.one_mul] at hMul
      omega
    · by_cases hgt : c₂ < c₁
      · have hMul : (c₂ + 1) * leavesPerCommittee ≤ c₁ * leavesPerCommittee :=
          Nat.mul_le_mul_right leavesPerCommittee hgt
        rw [Nat.add_mul, Nat.one_mul] at hMul
        omega
      · omega
  subst hc
  exact ⟨rfl, by omega⟩

end Qsag
end

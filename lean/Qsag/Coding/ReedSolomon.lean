module
public import Qsag.Coding.GuruswamiSudan
public import Qsag.Math.Goldilocks
public import Qsag.Tactic.Prelude

public section
namespace Qsag
open RoundPoly

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Constructive `LawfulField`, Fold Degree Invariant & 2-Point Affine Vandermonde Pruning -/


/-- One step of equal-degree affine binary folding (`Theorem 5.1`): two polynomials of degree `≤ d_j / 2`
    combine via `g(y) + (α + β y)(f(y) + θ g(y))` into degree `≤ d_j / 2 + 1`. -/
@[expose] def affineFoldDegreeStep (d : Nat) : Nat :=
  d / 2 + 1

/-- Iterated univariate degree bound across `s` equal-degree affine binary folds. -/
@[expose] def affineFoldDegreeIter : Nat → Nat → Nat
  | 0, d => d
  | s + 1, d => affineFoldDegreeIter s (affineFoldDegreeStep d)

private theorem affineFoldDegreeIter_le_of_le :
    ∀ (s m d : Nat), s ≤ m → d ≤ 2 ^ m + 1 → affineFoldDegreeIter s d ≤ 2 ^ (m - s) + 1
  | 0, m, d, _, hd => by simpa [affineFoldDegreeIter] using hd
  | s + 1, 0, _, hs, _ => by omega
  | s + 1, m + 1, d, hs, hd => by
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    have hstep : affineFoldDegreeStep d ≤ 2 ^ m + 1 := by
      unfold affineFoldDegreeStep
      omega
    have ih := affineFoldDegreeIter_le_of_le s m (affineFoldDegreeStep d) (by omega) hstep
    have hsub : m + 1 - (s + 1) = m - s := by omega
    rwa [hsub]

/-- **Equal-Degree Affine Fold Degree Stability (`affine_fold_degree_le_pow2_add_one`)**:
    Starting from multilinear univariate degree `d_0 = 2^ℓ - 1`, after ANY number `s ≤ ℓ` of
    equal-degree `[CWYZ26]` Theorem 5.1 folds (`d ↦ ⌊d/2⌋ + 1`), the folded polynomial has degree
    **`≤ 2^(ℓ - s) + 1`** — i.e., **at most `2` overflow monomials** (`2^(ℓ - s) + 2` coefficients),
    never growing unboundedly with `s`! -/
theorem affine_fold_degree_le_pow2_add_one (ℓ s : Nat) (hs : s ≤ ℓ) :
    affineFoldDegreeIter s (2 ^ ℓ - 1) ≤ 2 ^ (ℓ - s) + 1 := by
  have hpos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  exact affineFoldDegreeIter_le_of_le s ℓ (2 ^ ℓ - 1) hs (by omega)

/-- **Two-Point Affine Line Uniqueness (`affine_line_unique_of_two_points`)**:
    Over any `[LawfulField F] [DecidableEq F]`, if two affine functions `α₁ + β₁ x` and `α₂ + β₂ x`
    agree at two distinct points `z₀ ≠ z₁`, then `α₁ = α₂ ∧ β₁ = β₂`. -/
theorem affine_line_unique_of_two_points
    {F : Type} [LawfulField F] [DecidableEq F]
    {α₁ β₁ α₂ β₂ z₀ z₁ : F}
    (hz : z₀ ≠ z₁)
    (h₀ : CommRingOps.add α₁ (CommRingOps.mul β₁ z₀) =
          CommRingOps.add α₂ (CommRingOps.mul β₂ z₀))
    (h₁ : CommRingOps.add α₁ (CommRingOps.mul β₁ z₁) =
          CommRingOps.add α₂ (CommRingOps.mul β₂ z₁)) :
    α₁ = α₂ ∧ β₁ = β₂ := by
  have hdiff : CommRingOps.sub
      (CommRingOps.add α₁ (CommRingOps.mul β₁ z₀))
      (CommRingOps.add α₁ (CommRingOps.mul β₁ z₁)) =
      CommRingOps.sub
      (CommRingOps.add α₂ (CommRingOps.mul β₂ z₀))
      (CommRingOps.add α₂ (CommRingOps.mul β₂ z₁)) := by
    rw [h₀, h₁]
  have cancel_alpha : ∀ a x y : F,
      CommRingOps.sub (CommRingOps.add a x) (CommRingOps.add a y) = CommRingOps.sub x y := by
    intro a x y
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.add a y)
    rw [LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_assoc a y (CommRingOps.sub x y),
        LawfulCommRing.add_sub_cancel_left]
  rw [cancel_alpha α₁, cancel_alpha α₂,
      ← LawfulCommRing.mul_sub, ← LawfulCommRing.mul_sub] at hdiff
  have hprod : CommRingOps.mul (CommRingOps.sub β₁ β₂) (CommRingOps.sub z₀ z₁) =
      CommRingOps.zero := by
    rw [LawfulCommRing.sub_mul]
    exact LawfulCommRing.sub_eq_zero_iff.mpr hdiff
  have hzSub : CommRingOps.sub z₀ z₁ ≠ CommRingOps.zero :=
    fun h0 => hz (LawfulCommRing.sub_eq_zero_iff.mp h0)
  rcases LawfulField.mul_eq_zero hprod with hβ0 | hz0
  · have hβ : β₁ = β₂ := LawfulCommRing.sub_eq_zero_iff.mp hβ0
    subst hβ
    have hα : α₁ = α₂ := by
      apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul β₁ z₀)
      rw [LawfulCommRing.add_comm _ α₁, LawfulCommRing.add_comm _ α₂]
      exact h₀
    exact ⟨hα, rfl⟩
  · exact False.elim (hzSub hz0)

/-- Constructive `2 × 2` Vandermonde solver returning `(α, β)` with `α + β z₀ = y₀` and `α + β z₁ = y₁`. -/
def solveAffineLine {F : Type} [LawfulField F] (z₀ y₀ z₁ y₁ : F) : F × F :=
  let β := CommRingOps.mul (CommRingOps.sub y₀ y₁) (LawfulField.inv (CommRingOps.sub z₀ z₁))
  let α := CommRingOps.sub y₀ (CommRingOps.mul β z₀)
  (α, β)

theorem solveAffineLine_eq_of_eval
    {F : Type} [LawfulField F] [DecidableEq F]
    {α β z₀ y₀ z₁ y₁ : F}
    (hz : z₀ ≠ z₁)
    (h₀ : CommRingOps.add α (CommRingOps.mul β z₀) = y₀)
    (h₁ : CommRingOps.add α (CommRingOps.mul β z₁) = y₁) :
    (α, β) = solveAffineLine z₀ y₀ z₁ y₁ := by
  unfold solveAffineLine
  dsimp only
  have hzSub : CommRingOps.sub z₀ z₁ ≠ CommRingOps.zero :=
    fun h => hz (LawfulCommRing.sub_eq_zero_iff.mp h)
  let β' := CommRingOps.mul (CommRingOps.sub y₀ y₁) (LawfulField.inv (CommRingOps.sub z₀ z₁))
  let α' := CommRingOps.sub y₀ (CommRingOps.mul β' z₀)
  have h₀' : CommRingOps.add α' (CommRingOps.mul β' z₀) = y₀ := by
    dsimp [α']
    rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]
  have hDiff : CommRingOps.mul β' (CommRingOps.sub z₀ z₁) = CommRingOps.sub y₀ y₁ := by
    dsimp [β']
    rw [LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel hzSub, LawfulCommRing.mul_one]
  have h₁' : CommRingOps.add α' (CommRingOps.mul β' z₁) = y₁ := by
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.sub y₀ y₁)
    rw [LawfulCommRing.add_comm (CommRingOps.sub y₀ y₁) y₁,
        LawfulCommRing.add_sub_cancel_left,
        ← hDiff, LawfulCommRing.mul_sub,
        ← LawfulCommRing.add_assoc
            (CommRingOps.sub (CommRingOps.mul β' z₀) (CommRingOps.mul β' z₁)) α'
            (CommRingOps.mul β' z₁),
        LawfulCommRing.add_comm
            (CommRingOps.sub (CommRingOps.mul β' z₀) (CommRingOps.mul β' z₁)) α',
        LawfulCommRing.add_assoc α'
            (CommRingOps.sub (CommRingOps.mul β' z₀) (CommRingOps.mul β' z₁))
            (CommRingOps.mul β' z₁),
        LawfulCommRing.add_comm
            (CommRingOps.sub (CommRingOps.mul β' z₀) (CommRingOps.mul β' z₁))
            (CommRingOps.mul β' z₁),
        LawfulCommRing.add_sub_cancel_left,
        h₀']
  rcases affine_line_unique_of_two_points hz (h₀.trans h₀'.symm) (h₁.trans h₁'.symm) with ⟨rfl, rfl⟩
  rfl


/-- Affine duet discrepancy polynomial `Δ₀ + α Δ₁ + β Δ₂`. -/
@[expose] def evalAffineDuet {F : Type} [CommRingOps F] (Δ₀ Δ₁ Δ₂ α β : F) : F :=
  CommRingOps.add Δ₀ (CommRingOps.add (CommRingOps.mul α Δ₁) (CommRingOps.mul β Δ₂))

/-- **Affine Duet Root Bound (`affine_duet_roots_le_card`)**:
    Over any `[LawfulField F] [DecidableEq F]`, for any non-trivial discrepancy triple
    `(Δ₀, Δ₁, Δ₂) ≠ (0, 0, 0)` and duplicate-free challenge list `S`, at most `S.length` pairs
    `(α, β) ∈ prodPool S` satisfy `Δ₀ + α Δ₁ + β Δ₂ = 0` (`≤ |S| / |S|^2 = 1 / |S|` density). -/
theorem affine_duet_roots_le_card
    {F : Type} [LawfulField F] [DecidableEq F]
    (Δ₀ Δ₁ Δ₂ : F) (S : List F)
    (hS : S.Nodup)
    (hNonzero : Δ₀ ≠ CommRingOps.zero ∨ Δ₁ ≠ CommRingOps.zero ∨ Δ₂ ≠ CommRingOps.zero) :
    ((prodPool S).filter (fun p =>
      decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero))).length ≤ S.length := by
  if hΔ₂ : Δ₂ ≠ CommRingOps.zero then
    rw [prodPool_eq]
    have hbound := flatMap_filter_length_le
      (f := fun a => S.map (fun b => (a, b)))
      (p := fun p => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero))
      (B := 1) (xs := S) ?_
    · rw [Nat.mul_one] at hbound
      exact hbound
    · intro a haS
      let target := CommRingOps.neg
        (CommRingOps.mul (CommRingOps.add Δ₀ (CommRingOps.mul a Δ₁)) (LawfulField.inv Δ₂))
      have hmap : ((S.map (fun b => (a, b))).filter
          (fun p => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero))).length =
          (S.filter (fun b => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero))).length := by
        clear haS hS
        induction S with
        | nil => rfl
        | cons b bs ih =>
          simp only [List.map, List.filter]
          cases decide (evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero) <;>
            simp only [List.length_cons, ih]
      rw [hmap]
      have hsub := filter_sub_length_le
        (fun b => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero))
        (fun b => decide (b = target))
        (fun b hb => by
          have hev : evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero := of_decide_eq_true hb
          unfold evalAffineDuet at hev
          rw [← LawfulCommRing.add_assoc Δ₀ (CommRingOps.mul a Δ₁) (CommRingOps.mul b Δ₂)] at hev
          have hmul0 : CommRingOps.mul b Δ₂ =
              CommRingOps.neg (CommRingOps.add Δ₀ (CommRingOps.mul a Δ₁)) := by
            apply LawfulCommRing.add_left_cancel
              (a := CommRingOps.add Δ₀ (CommRingOps.mul a Δ₁))
            rw [LawfulCommRing.add_right_neg]
            exact hev
          have hbEq := congrArg (fun z => CommRingOps.mul z (LawfulField.inv Δ₂)) hmul0
          rw [LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hΔ₂, LawfulCommRing.mul_one,
              LawfulCommRing.neg_mul] at hbEq
          exact decide_eq_true hbEq)
        S
      exact Nat.le_trans hsub (filter_eq_max_one_of_nodup target hS)
  else
    have hΔ₂0 : Δ₂ = CommRingOps.zero :=
      if h : Δ₂ = CommRingOps.zero then h else False.elim (hΔ₂ h)
    if hΔ₁ : Δ₁ ≠ CommRingOps.zero then
      let target := CommRingOps.neg (CommRingOps.mul Δ₀ (LawfulField.inv Δ₁))
      let singlePairs := S.map (fun b => (target, b))
      have hndFilt : ((prodPool S).filter (fun p =>
          decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero))).Nodup := by
        have hndP := prodPool_nodup hS
        exact List.Pairwise.filter _ hndP
      have hsub : ∀ p ∈ (prodPool S).filter (fun p =>
          decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero)), p ∈ singlePairs := by
        intro p hp
        rw [List.mem_filter] at hp
        rcases hp with ⟨hpMem, hpZero⟩
        rcases p with ⟨a, b⟩
        have hbMem := (mem_prodPool_iff.mp hpMem).2
        have hev : evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero := of_decide_eq_true hpZero
        unfold evalAffineDuet at hev
        rw [hΔ₂0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hev
        have hmul0 : CommRingOps.mul a Δ₁ = CommRingOps.neg Δ₀ := by
          apply LawfulCommRing.add_left_cancel (a := Δ₀)
          rw [LawfulCommRing.add_right_neg]
          exact hev
        have haEq := congrArg (fun z => CommRingOps.mul z (LawfulField.inv Δ₁)) hmul0
        rw [LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hΔ₁, LawfulCommRing.mul_one,
            LawfulCommRing.neg_mul] at haEq
        subst haEq
        rw [List.mem_map]
        exact ⟨b, hbMem, rfl⟩
      have hle := nodup_length_le_of_subset hndFilt hsub
      simpa [singlePairs] using hle
    else
      have hΔ₁0 : Δ₁ = CommRingOps.zero :=
        if h : Δ₁ = CommRingOps.zero then h else False.elim (hΔ₁ h)
      have hΔ₀ : Δ₀ ≠ CommRingOps.zero := by
        rcases hNonzero with h0 | h1 | h2
        · exact h0
        · exact False.elim (hΔ₁ h1)
        · exact False.elim (hΔ₂ h2)
      have hempty : (prodPool S).filter (fun p =>
          decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero)) = [] := by
        induction prodPool S with
        | nil => rfl
        | cons p ps ih =>
          have hne : evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 ≠ CommRingOps.zero := by
            unfold evalAffineDuet
            rw [hΔ₁0, hΔ₂0, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
                LawfulCommRing.add_zero, LawfulCommRing.add_zero]
            exact hΔ₀
          simp [List.filter, hne, ih]
      rw [hempty]
      exact Nat.zero_le _

/-- Strictly ordered index pairs `(z₀, z₁)` from a domain list `D`, of exact size `D.length * (D.length - 1) / 2`. -/
def unorderedPairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ unorderedPairs xs

private theorem two_mul_unorderedPairs_length {α : Type} :
    ∀ (D : List α), 2 * (unorderedPairs D).length = D.length * (D.length - 1)
  | [] => rfl
  | x :: xs => by
    have ih := two_mul_unorderedPairs_length xs
    simp only [unorderedPairs, List.length_append, List.length_map, List.length_cons,
               Nat.add_sub_cancel]
    have hmul : (xs.length + 1) * xs.length = 2 * xs.length + xs.length * (xs.length - 1) := by
      cases xs with
      | nil => rfl
      | cons _ tl =>
        simp only [List.length_cons, Nat.add_sub_cancel]
        rw [Nat.add_mul, Nat.mul_add]
        omega
    omega

theorem unorderedPairs_length {α : Type} (D : List α) :
    (unorderedPairs D).length = D.length * (D.length - 1) / 2 := by
  rw [← two_mul_unorderedPairs_length D]
  omega

theorem ne_of_mem_unorderedPairs_nodup {α : Type} :
    ∀ {D : List α} {p : α × α}, D.Nodup → p ∈ unorderedPairs D → p.1 ≠ p.2
  | [], _, _, hp => by cases hp
  | x :: xs, ⟨a, b⟩, .cons hnot hnd, hp => by
    simp only [unorderedPairs, List.mem_append, List.mem_map, Prod.mk.injEq] at hp
    rcases hp with ⟨y, hy, rfl, rfl⟩ | htl
    · dsimp only
      exact fun heq => hnot x (heq ▸ hy) rfl
    · exact ne_of_mem_unorderedPairs_nodup hnd htl

private theorem filter_two_mem_unorderedPairs {α : Type} (pred : α → Bool) :
    ∀ {D : List α} {z₀ z₁ : α} {rest : List α},
      D.filter pred = z₀ :: z₁ :: rest → (z₀, z₁) ∈ unorderedPairs D
  | [], _, _, _, h => by cases h
  | x :: xs, z₀, z₁, rest, h => by
    simp only [List.filter] at h
    cases hpx : pred x
    · rw [hpx] at h
      have ih := filter_two_mem_unorderedPairs pred h
      simp only [unorderedPairs, List.mem_append]
      exact .inr ih
    · rw [hpx] at h
      injection h with hxEq htlEq
      subst hxEq
      have hz₁InFilt : z₁ ∈ xs.filter pred := by rw [htlEq]; exact .head _
      have hz₁InXs : z₁ ∈ xs := (List.mem_filter.mp hz₁InFilt).1
      simp only [unorderedPairs, List.mem_append, List.mem_map]
      exact .inl ⟨z₁, hz₁InXs, rfl⟩

/-- Predicate testing whether coordinate `z` is an **accidental agreement** between `(F, G)` and `(f, g)`
    along `(α, β)`: `F(z) + (α + β z) G(z) = f(z) + (α + β z) g(z)` while `(F(z), G(z)) ≠ (f(z), g(z))`. -/
@[expose] def isAccidentalAgreement
    {F : Type} [CommRingOps F] [DecidableEq F]
    (F_poly G_poly : List F) (f g : F → F) (α β z : F) : Bool :=
  let a := CommRingOps.add α (CommRingOps.mul β z)
  let lhs := CommRingOps.add (RoundPoly.evalCoeffs F_poly z)
    (CommRingOps.mul a (RoundPoly.evalCoeffs G_poly z))
  let rhs := CommRingOps.add (f z) (CommRingOps.mul a (g z))
  decide (lhs = rhs) &&
    !(decide (RoundPoly.evalCoeffs F_poly z = f z) && decide (RoundPoly.evalCoeffs G_poly z = g z))

private def pairLineCandidate
    {F : Type} [LawfulField F]
    (F_poly G_poly : List F) (f g : F → F) (pair : F × F) : F × F :=
  let ratio := fun z =>
    CommRingOps.mul
      (CommRingOps.sub (f z) (RoundPoly.evalCoeffs F_poly z))
      (LawfulField.inv (CommRingOps.sub (RoundPoly.evalCoeffs G_poly z) (g z)))
  solveAffineLine pair.1 (ratio pair.1) pair.2 (ratio pair.2)

private theorem accidental_agreement_forces_ratio
    {F : Type} [LawfulField F] [DecidableEq F]
    {F_poly G_poly : List F} {f g : F → F} {α β z : F}
    (hAcc : isAccidentalAgreement F_poly G_poly f g α β z = true) :
    CommRingOps.add α (CommRingOps.mul β z) =
      CommRingOps.mul
        (CommRingOps.sub (f z) (RoundPoly.evalCoeffs F_poly z))
        (LawfulField.inv (CommRingOps.sub (RoundPoly.evalCoeffs G_poly z) (g z))) := by
  unfold isAccidentalAgreement at hAcc
  rw [Bool.and_eq_true] at hAcc
  rcases hAcc with ⟨hEqDec, hNotBoth⟩
  have hEq : CommRingOps.add (RoundPoly.evalCoeffs F_poly z)
      (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (RoundPoly.evalCoeffs G_poly z)) =
      CommRingOps.add (f z)
      (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)) :=
    of_decide_eq_true hEqDec
  let a := CommRingOps.add α (CommRingOps.mul β z)
  let dG := CommRingOps.sub (RoundPoly.evalCoeffs G_poly z) (g z)
  let dF := CommRingOps.sub (f z) (RoundPoly.evalCoeffs F_poly z)
  have hRel : CommRingOps.mul a dG = dF := by
    dsimp [a, dG, dF]
    rw [LawfulCommRing.mul_sub]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add (RoundPoly.evalCoeffs F_poly z)
              (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)))
    rw [LawfulCommRing.add_assoc (RoundPoly.evalCoeffs F_poly z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)) _,
        LawfulCommRing.add_sub_cancel_left,
        hEq,
        LawfulCommRing.add_comm (RoundPoly.evalCoeffs F_poly z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)),
        LawfulCommRing.add_assoc
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z))
          (RoundPoly.evalCoeffs F_poly z) _,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_comm (f z) _]
  have hdGNe : dG ≠ CommRingOps.zero := by
    intro hdG0
    have hG : RoundPoly.evalCoeffs G_poly z = g z := LawfulCommRing.sub_eq_zero_iff.mp hdG0
    rw [hdG0, LawfulCommRing.mul_zero] at hRel
    have hF : RoundPoly.evalCoeffs F_poly z = f z :=
      (LawfulCommRing.sub_eq_zero_iff.mp hRel.symm).symm
    simp [hF, hG] at hNotBoth
  have hmul := congrArg (fun w => CommRingOps.mul w (LawfulField.inv dG)) hRel
  rw [LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hdGNe, LawfulCommRing.mul_one] at hmul
  exact hmul

/-- **Persistent Polynomial-Pair Pruning (`committed_polynomial_pair_bad_lines_le_choose2`)**:
    For ANY fixed polynomial pair `(F_poly, G_poly)` and ANY received words `(f, g)` on a
    duplicate-free domain `D : List F`, the number of challenge pairs `(α, β) ∈ prodPool S` with
    **at least `2` accidental agreements** in `D` (i.e., failing $s = 1$ coordinate inheritance)
    is bounded by **`D.length * (D.length - 1) / 2`**! -/
theorem committed_polynomial_pair_bad_lines_le_choose2
    {F : Type} [LawfulField F] [DecidableEq F]
    (F_poly G_poly : List F) (f g : F → F) (D S : List F)
    (hD : D.Nodup) (hS : S.Nodup) :
    ((prodPool S).filter (fun p =>
      decide (2 ≤ (D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2)).length))).length ≤
    D.length * (D.length - 1) / 2 := by
  let bad := (prodPool S).filter (fun p =>
    decide (2 ≤ (D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2)).length))
  let cands := (unorderedPairs D).map (pairLineCandidate F_poly G_poly f g)
  have hndBad : bad.Nodup := List.Pairwise.filter _ (prodPool_nodup hS)
  have hsub : ∀ p ∈ bad, p ∈ cands := by
    intro p hp
    rw [List.mem_filter] at hp
    rcases hp with ⟨_, hgeDec⟩
    have hge : 2 ≤ (D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2)).length :=
      of_decide_eq_true hgeDec
    cases hFilt : D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2) with
    | nil => rw [hFilt] at hge; cases hge
    | cons z₀ tl =>
      cases tl with
      | nil => rw [hFilt] at hge; cases hge; contradiction
      | cons z₁ rest =>
        have hPairMem : (z₀, z₁) ∈ unorderedPairs D :=
          filter_two_mem_unorderedPairs _ hFilt
        have hzNe : z₀ ≠ z₁ := ne_of_mem_unorderedPairs_nodup hD hPairMem
        have hz₀Acc : isAccidentalAgreement F_poly G_poly f g p.1 p.2 z₀ = true :=
          (List.mem_filter.mp (by rw [hFilt]; exact .head _)).2
        have hz₁Acc : isAccidentalAgreement F_poly G_poly f g p.1 p.2 z₁ = true :=
          (List.mem_filter.mp (by rw [hFilt]; exact .tail _ (.head _))).2
        have hpEq := solveAffineLine_eq_of_eval hzNe
          (accidental_agreement_forces_ratio hz₀Acc)
          (accidental_agreement_forces_ratio hz₁Acc)
        rw [List.mem_map]
        exact ⟨(z₀, z₁), hPairMem, hpEq.symm⟩
  have hle := nodup_length_le_of_subset hndBad hsub
  rw [List.length_map, unorderedPairs_length] at hle
  exact hle


/-- `HasAffineWitnessS1 d f g D α β P` holds when there exist polynomials `F_poly` (`deg ≤ d`,
    `length ≤ d + 1`) and `G_poly` (`deg ≤ d - 1`, `length ≤ d`) decomposing
    `P(X) = F_poly(X) + (α + β X) G_poly(X)` with at most `s = 1` disagreement coordinate on the
    agreement domain `S_{α,β}(P) ⊆ D` (`[CWYZ26]` Theorem 1.2 / Proposition 6.2). -/
@[expose] def HasAffineWitnessS1
    {F : Type} [CommRingOps F] [DecidableEq F]
    (d : Nat) (f g : F → F) (D : List F) (α β : F) (P : List F) : Prop :=
  ∃ F_poly G_poly : List F,
    F_poly.length ≤ d + 1 ∧
    G_poly.length ≤ d ∧
    (∀ x : F, RoundPoly.evalCoeffs P x =
      CommRingOps.add (RoundPoly.evalCoeffs F_poly x)
        (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β x))
          (RoundPoly.evalCoeffs G_poly x))) ∧
    let S_p := D.filter (fun z =>
      decide (RoundPoly.evalCoeffs P z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z))))
    (S_p.filter (fun z =>
      !(decide (RoundPoly.evalCoeffs F_poly z = f z) &&
        decide (RoundPoly.evalCoeffs G_poly z = g z)))).length ≤ 1

/-- **Constructive Welch–Berlekamp Affine Proximity-Gap Theorem (`welch_berlekamp_affine_proximity_gap`)**:
    Over ANY `[LawfulField F] [DecidableEq F]` (`0` algebraic geometry, `0` classical choice),
    whenever `A ≤ D.length` and `2 * D.length + d + 1 < 3 * A` (`δ < (1 - ρ) / 3`), for ANY received
    words `f, g : F → F`, ANY duplicate-free challenge list `S`, ANY duplicate-free subset
    `badPairs ⊆ prodPool S`, and ANY candidate map `P_of : F × F → List F` where every `p = (α, β) ∈ badPairs`
    has `(P_of p).length ≤ d + 1`, `A ≤ |S_{α,β}(P_of p)|`, and `¬ HasAffineWitnessS1 d f g D α β (P_of p)`:
    **`badPairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2)`**! -/

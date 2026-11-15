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
theorem welch_berlekamp_affine_proximity_gap
    {F : Type} [LawfulField F] [DecidableEq F]
    (f g : F → F) (D S : List F) (d A : Nat)
    (badPairs : List (F × F)) (P_of : F × F → List F)
    (hD : D.Nodup) (hS : S.Nodup)
    (hAD : A ≤ D.length)
    (hWB : 2 * D.length + d + 1 < 3 * A)
    (hBadNd : badPairs.Nodup)
    (hBadSub : ∀ p ∈ badPairs, p ∈ prodPool S)
    (hBadDeg : ∀ p ∈ badPairs, (P_of p).length ≤ d + 1)
    (hBadAgree : ∀ p ∈ badPairs,
      A ≤ (D.filter (fun z =>
        decide (RoundPoly.evalCoeffs (P_of p) z =
          CommRingOps.add (f z)
            (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z))))).length)
    (hBadExc : ∀ p ∈ badPairs, ¬ HasAffineWitnessS1 d f g D p.1 p.2 (P_of p)) :
    badPairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2) := by
  have hAd2 : d + 2 ≤ A := by omega
  -- 1. Build the `2 * D.length < 3 * A - d - 1` homogeneous WB system `Q(X, Y, Z) = u₀ + u₁ Y + Q₁ Z`:
  let N₀ := A
  let N₁ := A - 1
  let N₂ := A - d
  let N := N₀ + N₁ + N₂
  let rowF := fun (z : F) =>
    geomVec z N₀ ++ List.replicate N₁ CommRingOps.zero ++ (geomVec z N₂).map (CommRingOps.mul (f z))
  let rowG := fun (z : F) =>
    List.replicate N₀ CommRingOps.zero ++ geomVec z N₁ ++ (geomVec z N₂).map (CommRingOps.mul (g z))
  let rows := D.flatMap (fun z => [rowF z, rowG z])
  have hRowsLen : rows.length = 2 * D.length := by
    have aux : ∀ xs : List F, (xs.flatMap (fun z => [rowF z, rowG z])).length = 2 * xs.length := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x tl ih =>
        have hcons : (x :: tl).flatMap (fun z => [rowF z, rowG z]) =
            [rowF x, rowG x] ++ tl.flatMap (fun z => [rowF z, rowG z]) := List.flatMap_cons
        rw [hcons, List.length_append, ih]
        simp
        omega
    exact aux D
  have hRowsLt : rows.length < N := by
    rw [hRowsLen]; dsimp [N, N₀, N₁, N₂]; omega
  have hRowWidth : ∀ row ∈ rows, row.length = N := by
    intro row hmem
    dsimp [rows] at hmem
    rw [List.mem_flatMap] at hmem
    rcases hmem with ⟨z, _, hr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      · simp [rowF, rowG, List.length_append, geomVec_length, N]
        omega
  rcases gauss_nullspace_witness N rows hRowsLt hRowWidth with ⟨hvLen, hvAny, hvZero⟩
  let v := solveHomogeneous N rows
  have hvLen' : v.length = N₀ + N₁ + N₂ := hvLen
  let u₀ := v.take N₀
  let u₁ := (v.drop N₀).take N₁
  let Q₁ := v.drop (N₀ + N₁)
  have hu₀Len : u₀.length = N₀ := by
    dsimp only [u₀]
    exact List.length_take_of_le (by dsimp only [N₀, N₁, N₂] at hvLen' ⊢; omega)
  have hu₁Len : u₁.length = N₁ := by
    dsimp only [u₁]
    apply List.length_take_of_le
    rw [List.length_drop]
    dsimp only [N₀, N₁, N₂] at hvLen' ⊢
    omega
  have hQ₁Len : Q₁.length = N₂ := by
    dsimp only [Q₁]
    rw [List.length_drop]
    dsimp only [N₀, N₁, N₂] at hvLen' ⊢
    omega
  have hvSplit : v = (u₀ ++ u₁) ++ Q₁ := by
    have h1 : v = v.take N₀ ++ v.drop N₀ := (List.take_append_drop N₀ v).symm
    have h2 : v.drop N₀ = (v.drop N₀).take N₁ ++ (v.drop N₀).drop N₁ :=
      (List.take_append_drop N₁ (v.drop N₀)).symm
    rw [List.drop_drop] at h2
    calc v = u₀ ++ v.drop N₀ := h1
      _ = u₀ ++ (u₁ ++ Q₁) := congrArg (u₀ ++ ·) h2
      _ = (u₀ ++ u₁) ++ Q₁ := (List.append_assoc u₀ u₁ Q₁).symm
  have hInterpF : ∀ z ∈ D,
      CommRingOps.add (RoundPoly.evalCoeffs u₀ z)
        (CommRingOps.mul (f z) (RoundPoly.evalCoeffs Q₁ z)) = CommRingOps.zero := by
    intro z hz
    have h0 : dotVec (rowF z) v = CommRingOps.zero :=
      hvZero (rowF z) (List.mem_flatMap.mpr ⟨z, hz, .head _⟩)
    rw [hvSplit] at h0
    dsimp [rowF] at h0
    rw [dotVec_append_eq _ _ (u₀ ++ u₁) Q₁
          (by simp [List.length_append, geomVec_length, hu₀Len, hu₁Len]),
        dotVec_append_eq _ _ u₀ u₁ (by simp [geomVec_length, hu₀Len]),
        dotVec_geomVec_eq_evalCoeffs z N₀ u₀ hu₀Len,
        dotVec_replicate_zero, LawfulCommRing.add_zero,
        show List.map (CommRingOps.mul (f z)) (geomVec z N₂) = scaleVec (f z) (geomVec z N₂) from (scaleVec_eq _ _).symm,
        dotVec_scaleVec (f z),
        dotVec_geomVec_eq_evalCoeffs z N₂ Q₁ hQ₁Len] at h0
    exact h0
  have hInterpG : ∀ z ∈ D,
      CommRingOps.add (RoundPoly.evalCoeffs u₁ z)
        (CommRingOps.mul (g z) (RoundPoly.evalCoeffs Q₁ z)) = CommRingOps.zero := by
    intro z hz
    have h0 : dotVec (rowG z) v = CommRingOps.zero :=
      hvZero (rowG z) (List.mem_flatMap.mpr ⟨z, hz, .tail _ (.head _)⟩)
    rw [hvSplit] at h0
    dsimp [rowG] at h0
    rw [dotVec_append_eq _ _ (u₀ ++ u₁) Q₁
          (by simp [List.length_append, geomVec_length, hu₀Len, hu₁Len]),
        dotVec_append_eq _ _ u₀ u₁ (by simp [hu₀Len]),
        dotVec_replicate_zero, LawfulCommRing.zero_add,
        dotVec_geomVec_eq_evalCoeffs z N₁ u₁ hu₁Len,
        show List.map (CommRingOps.mul (g z)) (geomVec z N₂) = scaleVec (g z) (geomVec z N₂) from (scaleVec_eq _ _).symm,
        dotVec_scaleVec (g z),
        dotVec_geomVec_eq_evalCoeffs z N₂ Q₁ hQ₁Len] at h0
    exact h0
  have hQ₁Ne : trimPoly Q₁ ≠ [] := by
    intro hQ0
    have hQEval0 : ∀ z, RoundPoly.evalCoeffs Q₁ z = CommRingOps.zero := by
      intro z; rw [← evalCoeffs_trimPoly z Q₁, hQ0]; rfl
    have hu₀Nil : trimPoly u₀ = [] := by
      if hu0 : trimPoly u₀ = [] then exact hu0
      else
        rcases exists_nonroot_of_trim_ne_nil (isTrimmed_trimPoly u₀) hu0 hD
          (Nat.le_trans (trimPoly_length_le u₀) (by rw [hu₀Len]; exact hAD)) with ⟨z, hzD, hzNe⟩
        rw [evalCoeffs_trimPoly] at hzNe
        have hf := hInterpF z hzD
        rw [hQEval0 z, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hf
        exact False.elim (hzNe hf)
    have hu₁Nil : trimPoly u₁ = [] := by
      if hu1 : trimPoly u₁ = [] then exact hu1
      else
        rcases exists_nonroot_of_trim_ne_nil (isTrimmed_trimPoly u₁) hu1 hD
          (Nat.le_trans (trimPoly_length_le u₁) (by rw [hu₁Len]; dsimp only [N₁]; omega)) with ⟨z, hzD, hzNe⟩
        rw [evalCoeffs_trimPoly] at hzNe
        have hg := hInterpG z hzD
        rw [hQEval0 z, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hg
        exact False.elim (hzNe hg)
    have hallZero : ∀ w : List F, trimPoly w = [] → ∀ x ∈ w, x = CommRingOps.zero := by
      intro w hw x hx
      rcases List.getElem?_of_mem hx with ⟨idx, hidx⟩
      have hc := (trimPoly_eq_nil_iff w).mp hw idx
      simpa [coeffAt_eq_getD, List.getD, hidx] using hc
    rcases mem_of_any_true hvAny with ⟨x, hxMem, hxPred⟩
    change x ∈ v at hxMem
    rw [hvSplit, List.mem_append, List.mem_append] at hxMem
    have hx0 : x = CommRingOps.zero := by
      rcases hxMem with (hx0 | hx1) | hx2
      · exact hallZero u₀ hu₀Nil x hx0
      · exact hallZero u₁ hu₁Nil x hx1
      · exact hallZero Q₁ hQ0 x hx2
    simp [hx0] at hxPred
  let g12 := polyGcd u₁ Q₁
  let gcdPoly := polyGcd u₀ g12
  have hg12Spec := polyGcd_spec u₁ Q₁
  dsimp only at hg12Spec
  rcases hg12Spec with ⟨hg12Trim, hg12Dvd1, hg12DvdQ, hg12Univ⟩
  have hgcdSpec := polyGcd_spec u₀ g12
  dsimp only at hgcdSpec
  rcases hgcdSpec with ⟨hgcdTrim, hgcdDvd0, hgcdDvd12, hgcdUniv⟩
  change IsTrimmed gcdPoly at hgcdTrim
  rw [isTrimmed_iff] at hgcdTrim
  have hgcdDvd1 : DvdTrim gcdPoly u₁ := dvdTrim_trans hgcdDvd12 hg12Dvd1
  have hgcdDvdQ : DvdTrim gcdPoly Q₁ := dvdTrim_trans hgcdDvd12 hg12DvdQ
  have hgcdNe : trimPoly gcdPoly ≠ [] := by
    rw [hgcdTrim]
    intro h0
    change gcdPoly = [] at h0
    rw [dvdTrim_iff] at hgcdDvdQ
    rcases hgcdDvdQ with ⟨k, hk⟩
    rw [h0, (pMul_eq_nil_iff [] k).mpr (.inl (by rw [trimPoly_nil_eq]))] at hk
    exact hQ₁Ne hk
  have hex0 := exactDiv_of_dvdTrim u₀ gcdPoly hgcdNe hgcdDvd0
  have hex1 := exactDiv_of_dvdTrim u₁ gcdPoly hgcdNe hgcdDvd1
  have hexQ := exactDiv_of_dvdTrim Q₁ gcdPoly hgcdNe hgcdDvdQ
  dsimp only at hex0 hex1 hexQ
  rcases hex0 with ⟨hu0RedTrim, _, hu₀Fact⟩
  rcases hex1 with ⟨hu1RedTrim, _, hu₁Fact⟩
  rcases hexQ with ⟨hQ1RedTrim, _, hQ₁Fact⟩
  rw [isTrimmed_iff] at hu0RedTrim hu1RedTrim hQ1RedTrim
  let u0Red := (polyDivMod u₀ gcdPoly).1
  let u1Red := (polyDivMod u₁ gcdPoly).1
  let Q1Red := (polyDivMod Q₁ gcdPoly).1
  have hQ1RedNe : Q1Red ≠ [] := by
    intro h0
    change (polyDivMod Q₁ gcdPoly).1 = [] at h0
    rw [h0, (pMul_eq_nil_iff gcdPoly []).mpr (.inr (by rw [trimPoly_nil_eq]))] at hQ₁Fact
    exact hQ₁Ne hQ₁Fact
  have hCoprime : ∀ h : List F, IsTrimmed h →
      DvdTrim h u0Red → DvdTrim h u1Red → DvdTrim h Q1Red → h.length ≤ 1 := by
    intro h hhTrim hd0 hd1 hdQ
    rw [dvdTrim_iff] at hd0 hd1 hdQ
    if hhNil : h = [] then
      rw [hhNil]; simp
    else
      rcases hd0 with ⟨k0, hk0⟩
      rcases hd1 with ⟨k1, hk1⟩
      rcases hdQ with ⟨kQ, hkQ⟩
      rw [hu0RedTrim] at hk0; rw [hu1RedTrim] at hk1; rw [hQ1RedTrim] at hkQ
      have hdvd0 : DvdTrim (pMul gcdPoly h) u₀ :=
        (dvdTrim_iff _ _).mpr ⟨k0, by rw [hu₀Fact]; change _ = _; rw [hk0, pMul_assoc]⟩
      have hdvd1 : DvdTrim (pMul gcdPoly h) u₁ :=
        (dvdTrim_iff _ _).mpr ⟨k1, by rw [hu₁Fact]; change _ = _; rw [hk1, pMul_assoc]⟩
      have hdvdQ : DvdTrim (pMul gcdPoly h) Q₁ :=
        (dvdTrim_iff _ _).mpr ⟨kQ, by rw [hQ₁Fact]; change _ = _; rw [hkQ, pMul_assoc]⟩
      have hdvdGcd : DvdTrim (pMul gcdPoly h) gcdPoly :=
        hgcdUniv _ hdvd0 (hg12Univ _ hdvd1 hdvdQ)
      rw [dvdTrim_iff] at hdvdGcd
      rcases hdvdGcd with ⟨m, hm⟩
      change trimPoly gcdPoly = pMul (pMul gcdPoly h) m at hm
      rw [hgcdTrim, pMul_assoc] at hm
      have hhmNe : trimPoly (pMul h m) ≠ [] := by
        intro h0
        have h1 : pMul h m = [] := by
          have ht : trimPoly (pMul h m) = pMul h m := UPoly.pMul_trimmed _ _
          rwa [ht] at h0
        rw [h1, (pMul_eq_nil_iff gcdPoly []).mpr (.inr (by rw [trimPoly_nil_eq]))] at hm
        exact hgcdNe (by rw [hgcdTrim]; exact hm)
      have hgNeRaw : gcdPoly ≠ [] := by rwa [hgcdTrim] at hgcdNe
      have hgPos : 1 ≤ gcdPoly.length := by
        cases hgEq : gcdPoly with
        | nil => exact False.elim (hgNeRaw hgEq)
        | cons _ _ => simp
      have hlen1 := (pMul_length_of_trimmed_ne_nil ((isTrimmed_iff _).mpr hgcdTrim) (isTrimmed_trimPoly _) hgNeRaw
        (by simpa [trimPoly_idem] using hhmNe)).1
      rw [pMul_trimPoly_right, ← hm] at hlen1
      have hptHm : trimPoly (pMul h m) = pMul h m := UPoly.pMul_trimmed _ _
      rw [hptHm] at hlen1
      have hmNe : trimPoly m ≠ [] := by
        intro hm0
        rw [(pMul_eq_nil_iff h m).mpr (.inr hm0)] at hhmNe
        exact hhmNe trimPoly_nil_eq
      have hlen2 := (pMul_length_of_trimmed_ne_nil hhTrim (isTrimmed_trimPoly m) hhNil hmNe).1
      rw [pMul_trimPoly_right] at hlen2
      have hmPos : 1 ≤ (trimPoly m).length := by
        cases hmEq : trimPoly m with
        | nil => exact False.elim (hmNe hmEq)
        | cons _ _ => simp
      omega
  have hNegAdd : ∀ (x y : F),
      CommRingOps.add (CommRingOps.neg x) (CommRingOps.neg y) =
        CommRingOps.neg (CommRingOps.add x y) := by
    intro x y
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.add x y)
    rw [LawfulCommRing.add_right_neg,
        LawfulCommRing.add_assoc x y _,
        ← LawfulCommRing.add_assoc y (CommRingOps.neg x) (CommRingOps.neg y),
        LawfulCommRing.add_comm y (CommRingOps.neg x),
        LawfulCommRing.add_assoc (CommRingOps.neg x) y (CommRingOps.neg y),
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero,
        LawfulCommRing.add_right_neg]
  have hReduced : ∀ p ∈ badPairs,
      pAdd (pAdd u0Red (pMul [p.1, p.2] u1Red)) (pMul Q1Red (P_of p)) = [] := by
    intro p hpMem
    let R := pAdd (pAdd u₀ (pMul [p.1, p.2] u₁)) (pMul Q₁ (P_of p))
    have hRLen : R.length ≤ A := by
      have hL1 : (pMul [p.1, p.2] u₁).length ≤ A := by
        have h := pMul_length_le [p.1, p.2] u₁ 1 (A - 2) (by simp)
          (by rw [hu₁Len]; dsimp only [N₁]; omega)
        omega
      have hL2 : (pMul Q₁ (P_of p)).length ≤ A := by
        have h := pMul_length_le Q₁ (P_of p) (A - d - 1) d
          (by rw [hQ₁Len]; dsimp only [N₂]; omega) (hBadDeg p hpMem)
        omega
      exact pAdd_length_le _ _ A
        (pAdd_length_le _ _ A (by rw [hu₀Len]; exact Nat.le_refl A) hL1) hL2
    let S_p := D.filter (fun z =>
      decide (RoundPoly.evalCoeffs (P_of p) z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z))))
    have hSpNd : S_p.Nodup := List.Pairwise.filter _ hD
    have hSpLen : A ≤ S_p.length := hBadAgree p hpMem
    have hRZeroOnSp : ∀ z ∈ S_p, RoundPoly.evalCoeffs R z = CommRingOps.zero := by
      intro z hzSp
      rcases List.mem_filter.mp hzSp with ⟨hzD, hzAgDec⟩
      have hzAg : RoundPoly.evalCoeffs (P_of p) z =
          CommRingOps.add (f z)
            (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z)) :=
        of_decide_eq_true hzAgDec
      have hF0 := hInterpF z hzD
      have hG0 := hInterpG z hzD
      have hu₀Ev : RoundPoly.evalCoeffs u₀ z =
          CommRingOps.neg (CommRingOps.mul (f z) (RoundPoly.evalCoeffs Q₁ z)) := by
        apply LawfulCommRing.add_left_cancel
          (a := CommRingOps.mul (f z) (RoundPoly.evalCoeffs Q₁ z))
        rw [LawfulCommRing.add_right_neg, LawfulCommRing.add_comm]
        exact hF0
      have hu₁Ev : RoundPoly.evalCoeffs u₁ z =
          CommRingOps.neg (CommRingOps.mul (g z) (RoundPoly.evalCoeffs Q₁ z)) := by
        apply LawfulCommRing.add_left_cancel
          (a := CommRingOps.mul (g z) (RoundPoly.evalCoeffs Q₁ z))
        rw [LawfulCommRing.add_right_neg, LawfulCommRing.add_comm]
        exact hG0
      have hLinEv : RoundPoly.evalCoeffs [p.1, p.2] z =
          CommRingOps.add p.1 (CommRingOps.mul p.2 z) := by
        simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
              LawfulCommRing.mul_comm]
      dsimp [R]
      rw [evalCoeffs_pAdd, evalCoeffs_pAdd, evalCoeffs_pMul, evalCoeffs_pMul,
          hLinEv, hu₀Ev, hu₁Ev, hzAg]
      let lineVal := CommRingOps.add p.1 (CommRingOps.mul p.2 z)
      let qVal := RoundPoly.evalCoeffs Q₁ z
      change CommRingOps.add
        (CommRingOps.add (CommRingOps.neg (CommRingOps.mul (f z) qVal))
          (CommRingOps.mul lineVal (CommRingOps.neg (CommRingOps.mul (g z) qVal))))
        (CommRingOps.mul qVal (CommRingOps.add (f z) (CommRingOps.mul lineVal (g z)))) =
        CommRingOps.zero
      rw [LawfulCommRing.mul_neg, ← LawfulCommRing.mul_assoc lineVal (g z) qVal,
          hNegAdd, LawfulCommRing.left_distrib,
          LawfulCommRing.mul_comm qVal (f z), LawfulCommRing.mul_comm qVal _,
          LawfulCommRing.add_left_neg]
    have hRNil : R = [] := by
      if hRNe : R = [] then exact hRNe
      else
        have hRT : IsTrimmed R := isTrimmed_pAdd _ _
        rcases exists_nonroot_of_trim_ne_nil hRT hRNe hSpNd (Nat.le_trans hRLen hSpLen) with
          ⟨z, hzSp, hzNe⟩
        exact False.elim (hzNe (hRZeroOnSp z hzSp))
    have hRFact : R = pMul gcdPoly (pAdd (pAdd u0Red (pMul [p.1, p.2] u1Red)) (pMul Q1Red (P_of p))) := by
      dsimp [R, u0Red, u1Red, Q1Red]
      rw [← pAdd_trimPoly_left u₀, hu₀Fact,
          ← pMul_trimPoly_right [p.1, p.2] u₁, hu₁Fact,
          pMul_comm [p.1, p.2] (pMul gcdPoly (polyDivMod u₁ gcdPoly).1),
          pMul_assoc, pMul_comm (polyDivMod u₁ gcdPoly).1 [p.1, p.2],
          ← pMul_pAdd_right,
          ← pMul_trimPoly_left Q₁, hQ₁Fact, pMul_assoc,
          ← pMul_pAdd_right]
    rw [hRNil] at hRFact
    rcases (pMul_eq_nil_iff gcdPoly _).mp hRFact.symm with hg0 | hRed0
    · exact False.elim (hgcdNe hg0)
    · have hRedT : IsTrimmed (pAdd (pAdd u0Red (pMul [p.1, p.2] u1Red)) (pMul Q1Red (P_of p))) :=
        isTrimmed_pAdd _ _
      rw [isTrimmed_iff] at hRedT
      rwa [hRedT] at hRed0
  have hQ1RedPos : 1 ≤ Q1Red.length := by
    cases hEq : Q1Red with
    | nil => exact False.elim (hQ1RedNe hEq)
    | cons _ _ => simp
  if hQ1RedOne : Q1Red.length = 1 then
    have hQ1RedForm : ∃ c : F, Q1Red = [c] ∧ c ≠ CommRingOps.zero := by
      rcases hEqQ : Q1Red with _ | ⟨c, _ | _⟩
      · rw [hEqQ] at hQ1RedOne; cases hQ1RedOne
      · refine ⟨c, rfl, ?_⟩
        intro hc0; subst hc0
        have ht : IsTrimmed Q1Red := (isTrimmed_iff _).mpr hQ1RedTrim
        rw [hEqQ] at ht
        simp only [isTrimmed_iff, trimPoly_zero_singleton] at ht
        cases ht
      · rw [hEqQ] at hQ1RedOne; cases hQ1RedOne
    rcases hQ1RedForm with ⟨c, hQ1RedEq, hcNe⟩
    let negInvC := CommRingOps.neg (LawfulField.inv c)
    let F_poly := pScale negInvC u0Red
    let G_poly := pScale negInvC u1Red
    have hFT : trimPoly F_poly = F_poly := (isTrimmed_iff _).mp (isTrimmed_pScale _ _)
    have hGT : trimPoly G_poly = G_poly := (isTrimmed_iff _).mp (isTrimmed_pScale _ _)
    have hPEq : ∀ p ∈ badPairs, trimPoly (P_of p) = pAdd F_poly (pMul [p.1, p.2] G_poly) := by
      intro p hpMem
      have hRed := hReduced p hpMem
      rw [hQ1RedEq, pMul_singleton_eq] at hRed
      apply eq_of_isTrimmed_coeffAt _ _ (isTrimmed_trimPoly _) (isTrimmed_pAdd _ _)
      intro k
      have hc0 : coeffAt (pAdd (pAdd u0Red (pMul [p.1, p.2] u1Red)) (pScale c (P_of p))) k =
          CommRingOps.zero := by
        rw [hRed, coeffAt_nil]
      rw [coeffAt_pAdd, coeffAt_pAdd, coeffAt_pScale] at hc0
      have hmul := congrArg (CommRingOps.mul (LawfulField.inv c)) hc0
      rw [LawfulCommRing.mul_zero, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          ← LawfulCommRing.mul_assoc (LawfulField.inv c) c _,
          LawfulField.inv_mul_cancel hcNe, LawfulCommRing.one_mul] at hmul
      have hPval : coeffAt (P_of p) k =
          CommRingOps.add
            (CommRingOps.mul negInvC (coeffAt u0Red k))
            (CommRingOps.mul negInvC (coeffAt (pMul [p.1, p.2] u1Red) k)) := by
        dsimp [negInvC]
        rw [LawfulCommRing.neg_mul, LawfulCommRing.neg_mul, hNegAdd]
        apply LawfulCommRing.add_left_cancel
          (a := CommRingOps.add (CommRingOps.mul (LawfulField.inv c) (coeffAt u0Red k))
                  (CommRingOps.mul (LawfulField.inv c) (coeffAt (pMul [p.1, p.2] u1Red) k)))
        rw [LawfulCommRing.add_right_neg, hmul]
      rw [coeffAt_trimPoly, hPval]
      change _ = coeffAt (pAdd F_poly (pMul [p.1, p.2] G_poly)) k
      rw [coeffAt_pAdd,
          pMul_pScale_right negInvC [p.1, p.2] u1Red, coeffAt_pScale, coeffAt_pScale]
    if hDegFG : F_poly.length ≤ d + 1 ∧ G_poly.length ≤ d then
      have hSubBad : ∀ p ∈ badPairs,
          p ∈ (prodPool S).filter (fun q =>
            decide (2 ≤ (D.filter (isAccidentalAgreement F_poly G_poly f g q.1 q.2)).length)) := by
        intro p hpMem
        rw [List.mem_filter]
        refine ⟨hBadSub p hpMem, decide_eq_true ?_⟩
        have hPolyEq : ∀ x : F, RoundPoly.evalCoeffs (P_of p) x =
            CommRingOps.add (RoundPoly.evalCoeffs F_poly x)
              (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 x))
                (RoundPoly.evalCoeffs G_poly x)) := by
          intro x
          rw [← evalCoeffs_trimPoly x (P_of p), hPEq p hpMem, evalCoeffs_pAdd, evalCoeffs_pMul]
          simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
                LawfulCommRing.mul_comm]
        let S_p := D.filter (fun z =>
          decide (RoundPoly.evalCoeffs (P_of p) z =
            CommRingOps.add (f z)
              (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z))))
        let dis := S_p.filter (fun z =>
          !(decide (RoundPoly.evalCoeffs F_poly z = f z) &&
            decide (RoundPoly.evalCoeffs G_poly z = g z)))
        have hDisGe2 : 2 ≤ dis.length := by
          if hle1 : dis.length ≤ 1 then
            exact False.elim (hBadExc p hpMem ⟨F_poly, G_poly, hDegFG.1, hDegFG.2, hPolyEq, hle1⟩)
          else
            exact Nat.lt_of_not_ge hle1
        have hDisNd : dis.Nodup := List.Pairwise.filter _ (List.Pairwise.filter _ hD)
        have hDisSub : ∀ z ∈ dis, z ∈ D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2) := by
          intro z hz
          rcases List.mem_filter.mp hz with ⟨hzSp, hzNotBoth⟩
          rcases List.mem_filter.mp hzSp with ⟨hzD, hzAgDec⟩
          have hzAg := of_decide_eq_true hzAgDec
          rw [hPolyEq z] at hzAg
          rw [List.mem_filter]
          refine ⟨hzD, ?_⟩
          unfold isAccidentalAgreement
          simp [hzAg, hzNotBoth]
        exact Nat.le_trans hDisGe2 (nodup_length_le_of_subset hDisNd hDisSub)
      have hle := Nat.le_trans
        (nodup_length_le_of_subset hBadNd hSubBad)
        (committed_polynomial_pair_bad_lines_le_choose2 F_poly G_poly f g D S hD hS)
      exact Nat.le_trans hle (Nat.le_max_right _ _)
    else
      let mTop := Nat.max (F_poly.length - 1) G_poly.length
      have hmTopGe : d + 1 ≤ mTop := by
        if h1 : F_poly.length ≤ d + 1 then
          if h2 : G_poly.length ≤ d then
            exact False.elim (hDegFG ⟨h1, h2⟩)
          else
            exact Nat.le_trans (Nat.lt_of_not_ge h2) (Nat.le_max_right _ _)
        else
          have h2 : d + 1 ≤ F_poly.length - 1 := Nat.sub_le_sub_right (Nat.lt_of_not_ge h1) 1
          exact Nat.le_trans h2 (Nat.le_max_left _ _)
      have hmTopPos : 1 ≤ mTop := Nat.le_trans (Nat.le_add_left 1 d) hmTopGe
      let Δ₀ := coeffAt F_poly mTop
      let Δ₁ := coeffAt G_poly mTop
      let Δ₂ := coeffAt G_poly (mTop - 1)
      have hΔNz : Δ₀ ≠ CommRingOps.zero ∨ Δ₁ ≠ CommRingOps.zero ∨ Δ₂ ≠ CommRingOps.zero := by
        if hFG : G_poly.length ≤ F_poly.length - 1 then
          have hmEq : mTop = F_poly.length - 1 := Nat.max_eq_left hFG
          have hFNe : F_poly ≠ [] := by
            intro h0; rw [h0] at hmEq; rw [hmEq] at hmTopPos; cases hmTopPos
          have hLead := leadCoeff_ne_zero_of_trimPoly_ne_nil F_poly (by rwa [hFT])
          rw [hFT, ← hmEq] at hLead
          exact .inl hLead
        else
          have hmEq : mTop = G_poly.length :=
            Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hFG))
          have hGNe : G_poly ≠ [] := by
            intro h0; rw [h0] at hmEq; rw [hmEq] at hmTopPos; cases hmTopPos
          have hLead := leadCoeff_ne_zero_of_trimPoly_ne_nil G_poly (by rwa [hGT])
          rw [hGT] at hLead
          have hm1 : mTop - 1 = G_poly.length - 1 := congrArg (· - 1) hmEq
          exact .inr (.inr (by dsimp only [Δ₂]; rwa [hm1]))
      have hSubDuet : ∀ p ∈ badPairs,
          p ∈ (prodPool S).filter (fun q =>
            decide (evalAffineDuet Δ₀ Δ₁ Δ₂ q.1 q.2 = CommRingOps.zero)) := by
        intro p hpMem
        rw [List.mem_filter]
        refine ⟨hBadSub p hpMem, decide_eq_true ?_⟩
        have h0 : coeffAt (trimPoly (P_of p)) mTop = CommRingOps.zero := by
          rw [coeffAt_trimPoly]
          exact coeffAt_eq_zero_of_ge (P_of p) mTop (Nat.le_trans (hBadDeg p hpMem) hmTopGe)
        rw [hPEq p hpMem, pMul_linear_eq, coeffAt_pAdd, coeffAt_pAdd,
            coeffAt_pScale p.1 G_poly, coeffAt_pScale p.2 (CommRingOps.zero :: G_poly)] at h0
        have hShift : coeffAt (CommRingOps.zero :: G_poly) mTop = coeffAt G_poly (mTop - 1) := by
          cases hm : mTop with
          | zero => rw [hm] at hmTopPos; cases hmTopPos
          | succ m' => simp [coeffAt_cons_succ]
        rw [hShift] at h0
        simpa [evalAffineDuet, Δ₀, Δ₁, Δ₂] using h0
      have hle := Nat.le_trans
        (nodup_length_le_of_subset hBadNd hSubDuet)
        (affine_duet_roots_le_card Δ₀ Δ₁ Δ₂ S hS hΔNz)
      exact Nat.le_trans hle (Nat.le_max_left _ _)
  else
    have hQ1RedGe2 : 2 ≤ Q1Red.length := by
      if hle1 : Q1Red.length ≤ 1 then
        exact False.elim (hQ1RedOne (Nat.le_antisymm hle1 hQ1RedPos))
      else
        exact Nat.lt_of_not_ge hle1
    have hQ1RedTrimNe : trimPoly Q1Red ≠ [] := by rwa [hQ1RedTrim]
    have hSp0 := polyDivMod_spec u0Red Q1Red hQ1RedTrimNe
    have hSp1 := polyDivMod_spec u1Red Q1Red hQ1RedTrimNe
    have hSp2 := polyDivMod_spec (CommRingOps.zero :: u1Red) Q1Red hQ1RedTrimNe
    dsimp only at hSp0 hSp1 hSp2
    rcases hSp0 with ⟨_, hr₀T, hDiv0, hr₀Lt⟩
    rcases hSp1 with ⟨_, hr₁T, hDiv1, hr₁Lt⟩
    rcases hSp2 with ⟨_, hr₂T, hDiv2, hr₂Lt⟩
    let q₀ := (polyDivMod u0Red Q1Red).1
    let r₀ := (polyDivMod u0Red Q1Red).2
    let q₁ := (polyDivMod u1Red Q1Red).1
    let r₁ := (polyDivMod u1Red Q1Red).2
    let q₂ := (polyDivMod (CommRingOps.zero :: u1Red) Q1Red).1
    let r₂ := (polyDivMod (CommRingOps.zero :: u1Red) Q1Red).2
    change IsTrimmed r₀ at hr₀T
    change IsTrimmed r₁ at hr₁T
    change IsTrimmed r₂ at hr₂T
    rw [isTrimmed_iff] at hr₀T hr₁T hr₂T
    change trimPoly u0Red = pAdd (pMul q₀ Q1Red) r₀ at hDiv0
    change trimPoly u1Red = pAdd (pMul q₁ Q1Red) r₁ at hDiv1
    change trimPoly (CommRingOps.zero :: u1Red) = pAdd (pMul q₂ Q1Red) r₂ at hDiv2
    change r₀.length < (trimPoly Q1Red).length at hr₀Lt
    change r₁.length < (trimPoly Q1Red).length at hr₁Lt
    change r₂.length < (trimPoly Q1Red).length at hr₂Lt
    change trimPoly u0Red = u0Red at hu0RedTrim
    change trimPoly u1Red = u1Red at hu1RedTrim
    change trimPoly Q1Red = Q1Red at hQ1RedTrim
    rw [hu0RedTrim] at hDiv0
    rw [hu1RedTrim] at hDiv1
    rw [hQ1RedTrim] at hr₀Lt hr₁Lt hr₂Lt
    have hNotBothNil : ¬ (r₀ = [] ∧ r₁ = []) := by
      rintro ⟨hr0, hr1⟩
      have hd0 : DvdTrim Q1Red u0Red := by
        rw [dvdTrim_iff]
        have h := hDiv0
        rw [hr0, pAdd_nil_right, pMul_comm] at h
        have hpt : trimPoly (pMul Q1Red q₀) = pMul Q1Red q₀ := UPoly.pMul_trimmed _ _
        rw [hpt] at h
        exact ⟨q₀, by rw [hu0RedTrim]; exact h⟩
      have hd1 : DvdTrim Q1Red u1Red := by
        rw [dvdTrim_iff]
        have h := hDiv1
        rw [hr1, pAdd_nil_right, pMul_comm] at h
        have hpt : trimPoly (pMul Q1Red q₁) = pMul Q1Red q₁ := UPoly.pMul_trimmed _ _
        rw [hpt] at h
        exact ⟨q₁, by rw [hu1RedTrim]; exact h⟩
      have hle1 := hCoprime Q1Red ((isTrimmed_iff _).mpr hQ1RedTrim) hd0 hd1 (dvdTrim_refl Q1Red)
      omega
    let jIdx := if r₀ = [] then r₁.length - 1 else r₀.length - 1
    let Δ₀ := coeffAt r₀ jIdx
    let Δ₁ := coeffAt r₁ jIdx
    let Δ₂ := coeffAt r₂ jIdx
    have hΔNz : Δ₀ ≠ CommRingOps.zero ∨ Δ₁ ≠ CommRingOps.zero ∨ Δ₂ ≠ CommRingOps.zero := by
      if hr0 : r₀ = [] then
        have hr1Ne : r₁ ≠ [] := fun hr1 => hNotBothNil ⟨hr0, hr1⟩
        have hLead := leadCoeff_ne_zero_of_trimPoly_ne_nil r₁ (by rwa [hr₁T])
        rw [hr₁T] at hLead
        exact .inr (.inl (by simpa [Δ₁, jIdx, hr0] using hLead))
      else
        have hLead := leadCoeff_ne_zero_of_trimPoly_ne_nil r₀ (by rwa [hr₀T])
        rw [hr₀T] at hLead
        exact .inl (by simpa [Δ₀, jIdx, hr0] using hLead)
    have hSubDuet : ∀ p ∈ badPairs,
        p ∈ (prodPool S).filter (fun q =>
          decide (evalAffineDuet Δ₀ Δ₁ Δ₂ q.1 q.2 = CommRingOps.zero)) := by
      intro p hpMem
      rw [List.mem_filter]
      refine ⟨hBadSub p hpMem, decide_eq_true ?_⟩
      have hRed := hReduced p hpMem
      rw [pMul_linear_eq] at hRed
      let rComb := pAdd (pAdd r₀ (pScale p.1 r₁)) (pScale p.2 r₂)
      let qComb := pAdd (pAdd (pAdd q₀ (pScale p.1 q₁)) (pScale p.2 q₂)) (P_of p)
      have hCombLen : rComb.length ≤ Q1Red.length - 1 := by
        have h0L : r₀.length ≤ Q1Red.length - 1 := by omega
        have h1 : (pScale p.1 r₁).length ≤ Q1Red.length - 1 :=
          by
            rw [pScale_eq]
            exact Nat.le_trans (trimPoly_length_le _) (by rw [List.length_map]; omega)
        have h2 : (pScale p.2 r₂).length ≤ Q1Red.length - 1 :=
          by
            rw [pScale_eq]
            exact Nat.le_trans (trimPoly_length_le _) (by rw [List.length_map]; omega)
        exact pAdd_length_le _ _ (Q1Red.length - 1)
          (pAdd_length_le _ _ (Q1Red.length - 1) h0L h1) h2
      have hScaleAdd : ∀ (c : F) (x y : List F), pScale c (pAdd x y) = pAdd (pScale c x) (pScale c y) := by
        intro c x y
        simp only [pScale_eq, pAdd_eq]; rw [trimPoly_eq_iff_coeffAt]; intro k
        simp [coeffAt_map_mul, coeffAt_trimPoly, coeffAt_addCoeffs, LawfulCommRing.left_distrib]
      have hScaleTrim : ∀ (c : F) (x : List F), pScale c (trimPoly x) = pScale c x := by
        intro c x
        simp only [pScale_eq]; rw [trimPoly_eq_iff_coeffAt]; intro k
        simp [coeffAt_map_mul, coeffAt_trimPoly]
      have hScaleMulLeft : ∀ (c : F) (x y : List F), pScale c (pMul x y) = pMul (pScale c x) y := by
        intro c x y
        rw [pMul_comm x y, ← pMul_pScale_right, pMul_comm y (pScale c x)]
      have hSum0 : pAdd (pMul Q1Red qComb) rComb = [] := by
        have hLHS : pAdd (pAdd u0Red (pAdd (pScale p.1 u1Red) (pScale p.2 (CommRingOps.zero :: u1Red))))
            (pMul Q1Red (P_of p)) = pAdd (pMul Q1Red qComb) rComb := by
          rw [← hScaleTrim p.2 (CommRingOps.zero :: u1Red), hDiv2,
              hDiv0, hDiv1, hScaleAdd, hScaleAdd,
              hScaleMulLeft, hScaleMulLeft]
          simp only [pAdd_eq]
          rw [trimPoly_eq_iff_coeffAt]
          intro k
          simp only [coeffAt_addCoeffs, coeffAt_trimPoly, qComb, rComb, pAdd_eq]
          have hqExpand : coeffAt (pMul Q1Red (trimPoly (rawAddCoeffs
              (trimPoly (rawAddCoeffs
                (trimPoly (rawAddCoeffs q₀ (pScale p.1 q₁))) (pScale p.2 q₂)))
              (P_of p)))) k =
              CommRingOps.add
                (CommRingOps.add
                  (CommRingOps.add (coeffAt (pMul q₀ Q1Red) k) (coeffAt (pMul (pScale p.1 q₁) Q1Red) k))
                  (coeffAt (pMul (pScale p.2 q₂) Q1Red) k))
                (coeffAt (pMul Q1Red (P_of p)) k) := by
            simp only [← pAdd_eq]
            change coeffAt (pMul Q1Red qComb) k = _
            dsimp [qComb]
            rw [pMul_pAdd_right, pMul_pAdd_right, pMul_pAdd_right,
                coeffAt_pAdd, coeffAt_pAdd, coeffAt_pAdd,
                pMul_comm Q1Red q₀, pMul_comm Q1Red (pScale p.1 q₁), pMul_comm Q1Red (pScale p.2 q₂)]
          rw [hqExpand]
          let A0 := coeffAt (pMul q₀ Q1Red) k
          let R0 := coeffAt r₀ k
          let A1 := coeffAt (pMul (pScale p.1 q₁) Q1Red) k
          let R1 := coeffAt (pScale p.1 r₁) k
          let A2 := coeffAt (pMul (pScale p.2 q₂) Q1Red) k
          let R2 := coeffAt (pScale p.2 r₂) k
          let A3 := coeffAt (pMul Q1Red (P_of p)) k
          change CommRingOps.add (CommRingOps.add (CommRingOps.add A0 R0)
              (CommRingOps.add (CommRingOps.add A1 R1) (CommRingOps.add A2 R2))) A3 =
            CommRingOps.add (CommRingOps.add (CommRingOps.add (CommRingOps.add A0 A1) A2) A3)
              (CommRingOps.add (CommRingOps.add R0 R1) R2)
          have mid : CommRingOps.add (CommRingOps.add A1 R1) (CommRingOps.add A2 R2) =
              CommRingOps.add (CommRingOps.add A1 A2) (CommRingOps.add R1 R2) := by
            rw [LawfulCommRing.add_assoc A1 R1 _,
                ← LawfulCommRing.add_assoc R1 A2 R2,
                LawfulCommRing.add_comm R1 A2,
                LawfulCommRing.add_assoc A2 R1 R2,
                ← LawfulCommRing.add_assoc A1 A2 _]
          rw [mid]
          have left2 : CommRingOps.add (CommRingOps.add A0 R0)
              (CommRingOps.add (CommRingOps.add A1 A2) (CommRingOps.add R1 R2)) =
              CommRingOps.add (CommRingOps.add (CommRingOps.add A0 A1) A2)
                (CommRingOps.add (CommRingOps.add R0 R1) R2) := by
            rw [LawfulCommRing.add_assoc A0 R0 _,
                ← LawfulCommRing.add_assoc R0 (CommRingOps.add A1 A2) _,
                LawfulCommRing.add_comm R0 (CommRingOps.add A1 A2),
                LawfulCommRing.add_assoc (CommRingOps.add A1 A2) R0 _,
                ← LawfulCommRing.add_assoc A0 (CommRingOps.add A1 A2) _,
                ← LawfulCommRing.add_assoc A0 A1 A2,
                ← LawfulCommRing.add_assoc R0 R1 R2]
          rw [left2, LawfulCommRing.add_assoc _ _ A3,
              LawfulCommRing.add_comm (CommRingOps.add (CommRingOps.add R0 R1) R2) A3,
              ← LawfulCommRing.add_assoc]
        rw [← hLHS, hRed]
      have hrCombEq : rComb = pMul Q1Red (pNeg qComb) := by
        have hsub := pSub_pAdd_cancel_left (pMul Q1Red qComb) rComb
        have hrt : trimPoly rComb = rComb := UPoly.pAdd_trimmed _ _
        rw [hSum0, hrt] at hsub
        have hpt : trimPoly (pNeg (pMul Q1Red qComb)) = pNeg (pMul Q1Red qComb) := UPoly.pNeg_trimmed _
        rw [← hsub, pSub_eq_pAdd_pNeg, pAdd_nil_left, hpt, ← pMul_pNeg_right]
      have hrCombNil : rComb = [] := by
        if hrNe : rComb = [] then exact hrNe
        else
          have hqNe : trimPoly (pNeg qComb) ≠ [] := by
            intro h0
            rw [← pMul_trimPoly_right Q1Red, h0, (pMul_eq_nil_iff Q1Red []).mpr (.inr (by rw [trimPoly_nil_eq]))] at hrCombEq
            exact hrNe hrCombEq
          rw [← pMul_trimPoly_right Q1Red] at hrCombEq
          have hlen := (pMul_length_of_trimmed_ne_nil ((isTrimmed_iff _).mpr hQ1RedTrim) (isTrimmed_trimPoly _) hQ1RedNe hqNe).1
          rw [← hrCombEq] at hlen
          have hpos : 1 ≤ (trimPoly (pNeg qComb)).length := by
            cases h : trimPoly (pNeg qComb) with
            | nil => exact False.elim (hqNe h)
            | cons _ _ => simp
          omega
      have hc0 : coeffAt rComb jIdx = CommRingOps.zero := by rw [hrCombNil, coeffAt_nil]
      dsimp [rComb] at hc0
      rw [coeffAt_pAdd, coeffAt_pAdd, coeffAt_pScale p.1 r₁, coeffAt_pScale p.2 r₂,
          LawfulCommRing.add_assoc] at hc0
      exact hc0
    have hle := Nat.le_trans
      (nodup_length_le_of_subset hBadNd hSubDuet)
      (affine_duet_roots_le_card Δ₀ Δ₁ Δ₂ S hS hΔNz)
    exact Nat.le_trans hle (Nat.le_max_left _ _)

/-! ## §8. Constructive Candidate-List-Free Decoder (`gsDecodeList`, `0 Classical.choice`) -/

/-- All order-preserving sublists of `xs` of exact length `k`. -/
def sublistsOfLen {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (sublistsOfLen k xs).map (x :: ·) ++ sublistsOfLen (k + 1) xs

private theorem take_filter_mem_sublistsOfLen {α : Type} (pred : α → Bool) :
    ∀ (k : Nat) (xs : List α),
      k ≤ (xs.filter pred).length →
      (xs.filter pred).take k ∈ sublistsOfLen k xs
  | 0, _, _ => by simp [sublistsOfLen]
  | _ + 1, [], h => by simp at h
  | k + 1, x :: xs, h => by
    unfold sublistsOfLen
    rw [List.mem_append]
    cases hpx : pred x with
    | false =>
      simp only [List.filter, hpx] at h ⊢
      exact .inr (take_filter_mem_sublistsOfLen pred (k + 1) xs h)
    | true =>
      simp only [List.filter, hpx, List.length_cons, List.take] at h ⊢
      exact .inl (List.mem_map.mpr ⟨_, take_filter_mem_sublistsOfLen pred k xs (by omega), rfl⟩)

private theorem length_take_eq {α : Type} :
    ∀ (k : Nat) (xs : List α), k ≤ xs.length → (xs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: xs, h => by
    simp only [List.length_cons] at h
    simp only [List.take, List.length_cons, length_take_eq k xs (by omega)]

private theorem mem_of_mem_take {α : Type} :
    ∀ (k : Nat) {xs : List α} {z : α}, z ∈ xs.take k → z ∈ xs
  | 0, _, _, h => by cases h
  | _ + 1, [], _, h => by cases h
  | k + 1, _ :: xs, _, h => by
    simp only [List.take, List.mem_cons] at h
    rcases h with rfl | hm
    · exact .head _
    · exact .tail _ (mem_of_mem_take k hm)

private theorem nodup_take {α : Type} :
    ∀ (k : Nat) {xs : List α}, xs.Nodup → (xs.take k).Nodup
  | 0, _, _ => .nil
  | _ + 1, [], _ => .nil
  | k + 1, _ :: xs, hnd => by
    rcases hnd with _ | ⟨hnot, hnd'⟩
    simp only [List.take]
    exact List.Pairwise.cons (fun z hz heq => hnot z (mem_of_mem_take k hz) heq) (nodup_take k hnd')

/-- Constructive duplicate removal (`0` `Classical.choice`). -/
def dedupEq {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs =>
    let rest := dedupEq xs
    if x ∈ rest then rest else x :: rest

theorem mem_dedupEq {α : Type} [DecidableEq α] (z : α) :
    ∀ (xs : List α), z ∈ dedupEq xs ↔ z ∈ xs
  | [] => Iff.rfl
  | x :: xs => by
    unfold dedupEq
    dsimp only
    if hmem : x ∈ dedupEq xs then
      simp only [hmem, ↓reduceIte, List.mem_cons]
      constructor
      · intro hz; exact .inr ((mem_dedupEq z xs).mp hz)
      · rintro (rfl | hz)
        · exact hmem
        · exact (mem_dedupEq z xs).mpr hz
    else
      simp only [hmem, ↓reduceIte, List.mem_cons]
      exact or_congr Iff.rfl (mem_dedupEq z xs)

theorem dedupEq_nodup {α : Type} [DecidableEq α] :
    ∀ (xs : List α), (dedupEq xs).Nodup
  | [] => .nil
  | x :: xs => by
    unfold dedupEq
    dsimp only
    if hmem : x ∈ dedupEq xs then
      simp only [hmem, ↓reduceIte]
      exact dedupEq_nodup xs
    else
      simp only [hmem, ↓reduceIte]
      exact List.Pairwise.cons (fun z hz heq => hmem (heq ▸ hz)) (dedupEq_nodup xs)

/-- **Constructive Candidate-List-Free RS Decoder (`gsDecodeList`, `0 Classical.choice`)**:
    Over ANY `[LawfulField F] [DecidableEq F]` (without field finiteness or prover-supplied hints),
    computes the exact duplicate-free list of ALL canonical degree-`≤ d` polynomials agreeing with
    `word` on at least `A` points of `domain` (whenever `d + 1 ≤ A`). -/
def gsDecodeList {F : Type} [LawfulField F] [DecidableEq F]
    (d A : Nat) (domain : List F) (word : F → F) : List (GsUniPoly F) :=
  dedupEq (
    ((sublistsOfLen (d + 1) domain).map (fun pts => GsUniPoly.ofCoeffs (newtonInterp word pts))).filter
      (fun P => decide (P.coeffs.length ≤ d + 1 ∧
        A ≤ (domain.filter (fun x => decide (RoundPoly.evalCoeffs P.coeffs x = word x))).length)))

theorem gsDecodeList_nodup {F : Type} [LawfulField F] [DecidableEq F]
    (d A : Nat) (domain : List F) (word : F → F) :
    (gsDecodeList d A domain word).Nodup :=
  dedupEq_nodup _

/-- Exact completeness & soundness of `gsDecodeList`: whenever `domain.Nodup` and `d + 1 ≤ A`,
    a canonical polynomial `P : GsUniPoly F` belongs to `gsDecodeList d A domain word` **if and only if**
    `P.coeffs.length ≤ d + 1` and `P` agrees with `word` on at least `A` points of `domain`! -/
theorem mem_gsDecodeList_iff {F : Type} [LawfulField F] [DecidableEq F]
    {d A : Nat} {domain : List F} (word : F → F)
    (hDom : domain.Nodup) (hdA : d + 1 ≤ A) (P : GsUniPoly F) :
    P ∈ gsDecodeList d A domain word ↔
      (P.coeffs.length ≤ d + 1 ∧
        A ≤ (domain.filter (fun x => decide (RoundPoly.evalCoeffs P.coeffs x = word x))).length) := by
  unfold gsDecodeList
  rw [mem_dedupEq, List.mem_filter]
  constructor
  · rintro ⟨_, hdec⟩
    exact of_decide_eq_true hdec
  · rintro ⟨hDeg, hAgree⟩
    refine ⟨?_, decide_eq_true ⟨hDeg, hAgree⟩⟩
    let pred : F → Bool := fun x => decide (RoundPoly.evalCoeffs P.coeffs x = word x)
    let S := domain.filter pred
    have hSLen : d + 1 ≤ S.length := Nat.le_trans hdA hAgree
    let pts := S.take (d + 1)
    have hPtsSub : pts ∈ sublistsOfLen (d + 1) domain :=
      take_filter_mem_sublistsOfLen pred (d + 1) domain hSLen
    have hPtsLen : pts.length = d + 1 := length_take_eq (d + 1) S hSLen
    have hPtsNd : pts.Nodup := nodup_take (d + 1) (List.Pairwise.filter _ hDom)
    let Q : GsUniPoly F := GsUniPoly.ofCoeffs (newtonInterp word pts)
    have hQVal : Q.coeffs = newtonInterp word pts := by
      exact (GsUniPoly.ofCoeffs_coeffs_of_trimmed _ (newtonInterp_trimmed word pts))
    have hQDeg : Q.coeffs.length ≤ d + 1 := by
      rw [hQVal, ← hPtsLen]
      exact newtonInterp_length_le word pts
    have hPQEq : Q = P := by
      if hEq : Q = P then
        exact hEq
      else
        rcases gsUniPoly_exists_diff_on_domain hEq hQDeg hDeg hPtsNd
            (by rw [hPtsLen]; exact Nat.le_refl _) with
          ⟨x₀, hx₀Pts, hx₀Diff⟩
        have hx₀S : x₀ ∈ S := mem_of_mem_take (d + 1) hx₀Pts
        have hx₀P : RoundPoly.evalCoeffs P.coeffs x₀ = word x₀ :=
          of_decide_eq_true (List.mem_filter.mp hx₀S).2
        have hx₀Q : RoundPoly.evalCoeffs Q.coeffs x₀ = word x₀ := by
          rw [hQVal]
          exact evalCoeffs_newtonInterp word hPtsNd x₀ hx₀Pts
        exact False.elim (hx₀Diff (hx₀Q.trans hx₀P.symm))
    exact List.mem_map.mpr ⟨pts, hPtsSub, hPQEq⟩

/-- **Unconditional Guruswami–Sudan List Size Bound on `gsDecodeList`**:
    For ANY received word `word : F → F` on a `Nodup` domain `domain` and ANY valid GS parameter
    tuple `(d, A, D, m)` with `d + 1 ≤ A` and `domain.length * (m * (m + 1) / 2) < gsMonomialCount (m * A) d D`,
    the complete decoded list `gsDecodeList d A domain word` has length **`≤ D`**! -/
theorem gsDecodeList_length_le {F : Type} [LawfulField F] [DecidableEq F]
    (domain : List F) (word : F → F) (d A D m : Nat)
    (hDom : domain.Nodup)
    (hdA : d + 1 ≤ A)
    (hDim : domain.length * (m * (m + 1) / 2) < gsMonomialCount (m * A) d D) :
    (gsDecodeList d A domain word).length ≤ D := by
  refine guruswami_sudan_filter_list_bound domain word d A D m hDom hDim
    (gsDecodeList d A domain word) (gsDecodeList_nodup d A domain word) ?_
  intro P hP
  exact (mem_gsDecodeList_iff word hDom hdA P).mp hP

end Qsag

namespace Qsag
/-- **Parameter-Free Johnson List Size Bound on `gsDecodeList`**:
    Over any `[LawfulField F] [DecidableEq F]`, whenever `D.Nodup`, `d + 1 ≤ A`, and
    `D.length * d < A * A`, the complete decoded list `gsDecodeList d A D word` has length at most
    `JohnsonBound.johnsonBound D.length A d = (D.length * (A - d)) / (A * A - D.length * d)`. -/
theorem gsDecodeList_length_le_johnson {F : Type} [LawfulField F] [DecidableEq F]
    (D : List F) (word : F → F) (d A : Nat)
    (hD : D.Nodup) (hdA : d + 1 ≤ A) (hDen : D.length * d < A * A) :
    (gsDecodeList d A D word).length ≤ JohnsonBound.johnsonBound D.length A d := by
  let fam := gsDecodeList d A D word
  let memP : GsUniPoly F → F → Bool := fun P z => decide (RoundPoly.evalCoeffs P.coeffs z = word z)
  refine JohnsonBound.johnson_set_system_card_le D fam memP A d hD ?_ ?_ hDen
  · intro P hP
    exact ((mem_gsDecodeList_iff word hD hdA P).mp hP).2
  · refine JohnsonBound.pairwise_of_nodup (gsDecodeList_nodup d A D word) ?_
    intro P₁ hP₁ P₂ hP₂ hNe
    have h₁ := ((mem_gsDecodeList_iff word hD hdA P₁).mp hP₁).1
    have h₂ := ((mem_gsDecodeList_iff word hD hdA P₂).mp hP₂).1
    apply Decidable.byContradiction
    intro hGt
    have hULen : d + 1 ≤ (D.filter (fun z => memP P₁ z && memP P₂ z)).length := by omega
    have hUNd : (D.filter (fun z => memP P₁ z && memP P₂ z)).Nodup := List.Pairwise.filter _ hD
    obtain ⟨x₀, hx₀U, hx₀Diff⟩ := gsUniPoly_exists_diff_on_domain hNe h₁ h₂ hUNd hULen
    rcases (Bool.and_eq_true _ _).mp (List.mem_filter.mp hx₀U).2 with ⟨he₁, he₂⟩
    exact hx₀Diff ((of_decide_eq_true he₁).trans (of_decide_eq_true he₂).symm)


end Qsag

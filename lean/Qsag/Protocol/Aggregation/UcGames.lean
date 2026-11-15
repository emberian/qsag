module
/-
# Qsag.UcGames — Finite `KeyedLazyRO`, Shamir Pad-Space Bijections & Canetti UC Signatures

Self-contained Lean 4.35 game-hopping, secret-sharing simulation, and UC signature foundations:
1. Finite query-bounded `OracleComp` decision trees, slice reprogramming (`condProb_pin_untouched`),
   unified leaf+Merkle birthday bound (`unifiedTreeGame_birthday_le`), keyed-ROM hiding floor
   (`hidingAdv_le`, `hidingAdv_le_deployed`) at exact deployed cardinalities (`2^256` vs `p^4`,
   `deployedCardGoldilocks4_ne_bitVec256`), and 3-regime query characterization
   (`lazyRo_query_regime_characterization`).
2. Polymorphic Shamir pad-space bijection (`shamir_rebalanceEquiv`,
   `pad_bijection_masked_openings_uniform`) over `Goldilocks`, `GoldilocksExt2`, and `TowerElem k`
   with characteristic-2 involution (`shamir_tower_rebalance_involutive`), collusion threshold teeth
   (`full_collusion_breaks_hiding`, `tooth_unpadded_open_refutes_hiding`), and Vandermonde-at-zero
   reconstruction (`lagrangeAtZero_evalCoeffs`).
3. Signature functionality `idealSig` and one game hop against it
   (`sigOracleGameHop_distinguisher_iff_forgery`): the ideal world is handed a signing oracle
   `simSign` that is assumed to answer exactly as the real signer does, and the hop shows that a
   real/ideal difference is a fresh forgery. No simulator without the signing key is constructed
   in this module, so this is not a UC-realization theorem. Its per-session and per-caller
   corollaries are `multi_session_uc_realizes` and `uc_composition_theorem`.
-/

public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Qrom
public import Qsag.Math.Gf2Pow128
public import Qsag.Oracle.Poseidon2

public section
namespace Qsag

set_option autoImplicit false

/-! ## 2. Polymorphic Shamir Pad-Space Bijection (`Goldilocks`, `GoldilocksExt2`, `TowerElem k`) -/

section PolymorphicPadBijection
open CommRingOps

def polyAddFixed {R : Type} [CommRingOps R] : List R → List R → List R
  | a :: as, b :: bs => add a b :: polyAddFixed as bs
  | [], _ => []
  | _, [] => []

def polySubFixed {R : Type} [CommRingOps R] : List R → List R → List R
  | a :: as, b :: bs => sub a b :: polySubFixed as bs
  | [], _ => []
  | _, [] => []

def polyScale {R : Type} [CommRingOps R] (s : R) : List R → List R
  | [] => []
  | c :: cs => mul s c :: polyScale s cs

theorem polyAddFixed_length {R : Type} [CommRingOps R] :
    ∀ (p q : List R), p.length = q.length → (polyAddFixed p q).length = p.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polyAddFixed, polyAddFixed_length as bs h]

theorem polySubFixed_length {R : Type} [CommRingOps R] :
    ∀ (p q : List R), p.length = q.length → (polySubFixed p q).length = p.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polySubFixed, polySubFixed_length as bs h]

theorem polyScale_length {R : Type} [CommRingOps R] (s : R) (p : List R) :
    (polyScale s p).length = p.length := by
  induction p <;> simp [polyScale, *]

private theorem add_sub_cancel_right {R : Type} [LawfulCommRing R] (a b : R) :
    sub (add a b) b = a := by
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
      LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

private theorem sub_add_cancel_right {R : Type} [LawfulCommRing R] (a b : R) :
    add (sub a b) b = a := by
  rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]

theorem polySub_polyAdd_cancel {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R), p.length = q.length → polySubFixed (polyAddFixed p q) q = p
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polyAddFixed, polySubFixed, add_sub_cancel_right, polySub_polyAdd_cancel as bs h]

theorem polyAdd_polySub_cancel {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R), p.length = q.length → polyAddFixed (polySubFixed p q) q = p
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polyAddFixed, polySubFixed, sub_add_cancel_right, polyAdd_polySub_cancel as bs h]

theorem evalCoeffs_addFixed {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R) (x : R), p.length = q.length →
      RoundPoly.evalCoeffs (polyAddFixed p q) x =
        add (RoundPoly.evalCoeffs p x) (RoundPoly.evalCoeffs q x)
  | [], [], _, _ => by simp [polyAddFixed, LawfulCommRing.add_zero]
  | a :: as, b :: bs, x, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [polyAddFixed, RoundPoly.evalCoeffs_cons, evalCoeffs_addFixed as bs x h]
    rw [LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

theorem evalCoeffs_subFixed {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R) (x : R), p.length = q.length →
      RoundPoly.evalCoeffs (polySubFixed p q) x =
        sub (RoundPoly.evalCoeffs p x) (RoundPoly.evalCoeffs q x)
  | [], [], _, _ => by simp [polySubFixed, LawfulCommRing.sub_self]
  | a :: as, b :: bs, x, h => by
    have hLen : (polySubFixed (a :: as) (b :: bs)).length = (b :: bs).length := by
      rw [polySubFixed_length (a :: as) (b :: bs) h, h]
    have hEq := evalCoeffs_addFixed (polySubFixed (a :: as) (b :: bs)) (b :: bs) x hLen
    rw [polyAdd_polySub_cancel (a :: as) (b :: bs) h] at hEq
    have hSub := congrArg (fun u => sub u (RoundPoly.evalCoeffs (b :: bs) x)) hEq
    rw [add_sub_cancel_right] at hSub
    exact hSub.symm

theorem evalCoeffs_scale {R : Type} [LawfulCommRing R] (s : R) :
    ∀ (p : List R) (x : R),
      RoundPoly.evalCoeffs (polyScale s p) x = mul s (RoundPoly.evalCoeffs p x)
  | [], _ => by simp [polyScale, LawfulCommRing.mul_zero]
  | c :: cs, x => by
    simp only [polyScale, RoundPoly.evalCoeffs_cons, evalCoeffs_scale s cs x]
    rw [LawfulCommRing.left_distrib, ← LawfulCommRing.mul_assoc x s _,
        LawfulCommRing.mul_comm x s, LawfulCommRing.mul_assoc s x _]

private def mulLinearAux {R : Type} [CommRingOps R] (k prev : R) : List R → List R
  | [] => [prev]
  | c :: cs => add c prev :: mulLinearAux k (mul k c) cs

def mulOnePlusKX {R : Type} [CommRingOps R] (k : R) : List R → List R
  | [] => []
  | c :: cs => c :: mulLinearAux k (mul k c) cs

private theorem mulLinearAux_length {R : Type} [CommRingOps R] (k prev : R) :
    ∀ (cs : List R), (mulLinearAux k prev cs).length = cs.length + 1
  | [] => rfl
  | _ :: cs => by simp [mulLinearAux, mulLinearAux_length k _ cs]

theorem mulOnePlusKX_length {R : Type} [CommRingOps R] (k : R) :
    ∀ (p : List R), p ≠ [] → (mulOnePlusKX k p).length = p.length + 1
  | [], h => False.elim (h rfl)
  | _ :: _, _ => by simp [mulOnePlusKX, mulLinearAux_length]

private theorem evalCoeffs_mulLinearAux {R : Type} [LawfulCommRing R] (k prev : R) :
    ∀ (cs : List R) (x : R),
      RoundPoly.evalCoeffs (mulLinearAux k prev cs) x =
        add prev (mul (add one (mul k x)) (RoundPoly.evalCoeffs cs x))
  | [], _ => by
    simp [mulLinearAux, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | c :: cs, x => by
    simp only [mulLinearAux, RoundPoly.evalCoeffs_cons, evalCoeffs_mulLinearAux k (mul k c) cs x]
    rw [LawfulCommRing.left_distrib x, LawfulCommRing.left_distrib (add one (mul k x)),
        LawfulCommRing.right_distrib one (mul k x) c, LawfulCommRing.one_mul]
    have hxc : mul x (mul k c) = mul (mul k x) c := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x k]
    have hxs : mul x (mul (add one (mul k x)) (RoundPoly.evalCoeffs cs x)) =
        mul (add one (mul k x)) (mul x (RoundPoly.evalCoeffs cs x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x (add one (mul k x)),
          LawfulCommRing.mul_assoc]
    rw [hxc, hxs, LawfulCommRing.add_comm c prev, LawfulCommRing.add_assoc prev c,
        LawfulCommRing.add_assoc c (mul (mul k x) c)]

theorem evalCoeffs_mulOnePlusKX {R : Type} [LawfulCommRing R] (k : R) :
    ∀ (p : List R) (x : R),
      RoundPoly.evalCoeffs (mulOnePlusKX k p) x =
        mul (add one (mul k x)) (RoundPoly.evalCoeffs p x)
  | [], _ => by simp [mulOnePlusKX, LawfulCommRing.mul_zero]
  | c :: cs, x => by
    simp only [mulOnePlusKX, RoundPoly.evalCoeffs_cons, evalCoeffs_mulLinearAux]
    rw [LawfulCommRing.left_distrib x, LawfulCommRing.left_distrib (add one (mul k x)),
        LawfulCommRing.right_distrib one (mul k x) c, LawfulCommRing.one_mul, ← LawfulCommRing.add_assoc]
    have hxc : mul x (mul k c) = mul (mul k x) c := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x k]
    have hxs : mul x (mul (add one (mul k x)) (RoundPoly.evalCoeffs cs x)) =
        mul (add one (mul k x)) (mul x (RoundPoly.evalCoeffs cs x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x (add one (mul k x)),
          LawfulCommRing.mul_assoc]
    rw [hxc, hxs]

def vanishCorruptRaw {R : Type} [CommRingOps R] (inv : R → R) : List R → List R
  | [] => [one]
  | xc :: rest => mulOnePlusKX (neg (inv xc)) (vanishCorruptRaw inv rest)

theorem vanishCorruptRaw_nonempty {R : Type} [CommRingOps R] (inv : R → R) :
    ∀ (cs : List R), vanishCorruptRaw inv cs ≠ []
  | [] => by simp [vanishCorruptRaw]
  | _ :: rest => by
    have ih := vanishCorruptRaw_nonempty inv rest
    cases h : vanishCorruptRaw inv rest with
    | nil => exact False.elim (ih h)
    | cons c cs => simp [vanishCorruptRaw, h, mulOnePlusKX]

theorem vanishCorruptRaw_length {R : Type} [CommRingOps R] (inv : R → R) :
    ∀ (cs : List R), (vanishCorruptRaw inv cs).length = cs.length + 1
  | [] => rfl
  | _ :: rest => by
    simp only [vanishCorruptRaw, List.length_cons]
    rw [mulOnePlusKX_length _ _ (vanishCorruptRaw_nonempty inv rest), vanishCorruptRaw_length inv rest]

theorem evalCoeffs_replicate_zero {R : Type} [LawfulCommRing R] :
    ∀ (k : Nat) (x : R), RoundPoly.evalCoeffs (List.replicate k (zero : R)) x = zero
  | 0, _ => rfl
  | k + 1, x => by
    simp [List.replicate_succ, evalCoeffs_replicate_zero k x,
          LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

theorem evalCoeffs_padZerosRight {R : Type} [LawfulCommRing R] :
    ∀ (p : List R) (k : Nat) (x : R),
      RoundPoly.evalCoeffs (p ++ List.replicate k (zero : R)) x = RoundPoly.evalCoeffs p x
  | [], _, _ => by simp [evalCoeffs_replicate_zero]
  | _ :: cs, k, x => by simp [List.cons_append, evalCoeffs_padZerosRight cs k x]

def vanishCorruptUnit0 {R : Type} [CommRingOps R] (inv : R → R) (t : Nat) (corruptPts : List R) : List R :=
  let raw := vanishCorruptRaw inv corruptPts
  raw ++ List.replicate (t - raw.length) zero

theorem vanishCorruptUnit0_props {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    {t : Nat} {corruptPts : List R}
    (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero) :
    (vanishCorruptUnit0 inv t corruptPts).length = t ∧
    RoundPoly.evalCoeffs (vanishCorruptUnit0 inv t corruptPts) zero = one ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs (vanishCorruptUnit0 inv t corruptPts) xc = zero) := by
  have hRawLen := vanishCorruptRaw_length inv corruptPts
  have hAtZero : ∀ cs : List R, RoundPoly.evalCoeffs (vanishCorruptRaw inv cs) zero = one := by
    intro cs
    induction cs with
    | nil =>
      simp [vanishCorruptRaw, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    | cons xc rest ih =>
      simp [vanishCorruptRaw, evalCoeffs_mulOnePlusKX, ih,
            LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.mul_one]
  have hAtCorr : ∀ {cs : List R} {x : R},
      (∀ c ∈ cs, c ≠ zero) → x ∈ cs → RoundPoly.evalCoeffs (vanishCorruptRaw inv cs) x = zero := by
    intro cs x hNz hx
    induction cs with
    | nil => cases hx
    | cons xc rest ih =>
      simp only [vanishCorruptRaw, evalCoeffs_mulOnePlusKX]
      rcases List.mem_cons.mp hx with rfl | hMemRest
      · have hxNz : x ≠ zero := hNz x (.head rest)
        have hFactor : add one (mul (neg (inv x)) x) = zero := by
          rw [LawfulCommRing.neg_mul, LawfulCommRing.mul_comm (inv x) x,
              hInv x hxNz, LawfulCommRing.add_right_neg]
        rw [hFactor, LawfulCommRing.zero_mul]
      · rw [ih (fun c hc => hNz c (.tail xc hc)) hMemRest, LawfulCommRing.mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · unfold vanishCorruptUnit0
    dsimp only
    rw [List.length_append, List.length_replicate, hRawLen]
    omega
  · unfold vanishCorruptUnit0
    dsimp only
    rw [evalCoeffs_padZerosRight, hAtZero]
  · intro xc hxc
    unfold vanishCorruptUnit0
    dsimp only
    rw [evalCoeffs_padZerosRight]
    exact hAtCorr hNonZero hxc

abbrev ShamirPadPoly (R : Type) (t : Nat) := { p : List R // p.length = t }

/-- **Constructive Polymorphic Shamir Pad-Space Bijection (`shamir_rebalanceEquiv`)**. -/
@[expose] def shamir_rebalanceEquiv {R : Type} [LawfulCommRing R]
    (inv : R → R) (t : Nat) (corruptPts : List R)
    (w : R) (hCard : corruptPts.length + 1 ≤ t) :
    SimpleEquiv (ShamirPadPoly R t) (ShamirPadPoly R t) :=
  let delta := polyScale w (vanishCorruptUnit0 inv t corruptPts)
  have hDeltaLen : delta.length = t := by
    rw [polyScale_length]
    unfold vanishCorruptUnit0; dsimp only
    rw [List.length_append, List.length_replicate, vanishCorruptRaw_length]
    omega
  { toFun := fun ⟨p, hp⟩ => ⟨polyAddFixed p delta, by rw [polyAddFixed_length p delta (hp.trans hDeltaLen.symm), hp]⟩
    invFun := fun ⟨q, hq⟩ => ⟨polySubFixed q delta, by rw [polySubFixed_length q delta (hq.trans hDeltaLen.symm), hq]⟩
    left_inv := fun ⟨p, hp⟩ => Subtype.ext (polySub_polyAdd_cancel p delta (hp.trans hDeltaLen.symm))
    right_inv := fun ⟨q, hq⟩ => Subtype.ext (polyAdd_polySub_cancel q delta (hq.trans hDeltaLen.symm)) }

theorem shamir_tower_rebalance_involutive (k t : Nat)
    (corruptPts : List (TowerElem k)) (w : TowerElem k)
    (hCard : corruptPts.length + 1 ≤ t)
    (P : ShamirPadPoly (TowerElem k) t) :
    let eqv := shamir_rebalanceEquiv (towerInv k) t corruptPts w hCard
    eqv.toFun (eqv.toFun P) = P := by
  intro eqv
  have hAddEqSub : ∀ (u v : List (TowerElem k)), polyAddFixed u v = polySubFixed u v := by
    intro u v
    induction u generalizing v with
    | nil => cases v <;> rfl
    | cons a as ih =>
      cases v with
      | nil => rfl
      | cons b bs =>
        simp only [polyAddFixed, polySubFixed]
        exact congrArg (towerAdd k a b :: ·) (ih bs)
  have hEqInv : eqv.toFun (eqv.toFun P) = eqv.invFun (eqv.toFun P) := by
    apply Subtype.ext
    exact hAddEqSub _ _
  rw [hEqInv, eqv.left_inv]

/-- **Pad-Space Bijection Uniformity & Zero-Knowledge Theorem (`pad_bijection_masked_openings_uniform`)**. -/
theorem pad_bijection_masked_openings_uniform {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (t : Nat) (corruptPts : List R)
    (w : R) (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero)
    (P : ShamirPadPoly R t) :
    let Q := (shamir_rebalanceEquiv inv t corruptPts w hCard).toFun P
    add zero (RoundPoly.evalCoeffs Q.1 zero) =
      add w (RoundPoly.evalCoeffs P.1 zero) ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs Q.1 xc = RoundPoly.evalCoeffs P.1 xc) := by
  intro Q
  obtain ⟨hULen, hU0, hUCorr⟩ := vanishCorruptUnit0_props inv hInv hCard hNonZero
  have hScaleLen : (polyScale w (vanishCorruptUnit0 inv t corruptPts)).length = t := by
    rw [polyScale_length, hULen]
  refine ⟨?_, ?_⟩
  · change add zero
      (RoundPoly.evalCoeffs (polyAddFixed P.1 (polyScale w (vanishCorruptUnit0 inv t corruptPts))) zero) = _
    rw [evalCoeffs_addFixed P.1 _ _ (P.2.trans hScaleLen.symm), evalCoeffs_scale, hU0,
        LawfulCommRing.zero_add, LawfulCommRing.mul_one, LawfulCommRing.add_comm]
  · intro xc hxc
    change RoundPoly.evalCoeffs (polyAddFixed P.1 (polyScale w (vanishCorruptUnit0 inv t corruptPts))) xc = _
    rw [evalCoeffs_addFixed P.1 _ _ (P.2.trans hScaleLen.symm), evalCoeffs_scale, hUCorr xc hxc,
        LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

theorem pad_bijection_goldilocks_and_tower (k t : Nat)
    (corrGl : List Goldilocks) (wGl : Goldilocks)
    (hCardGl : corrGl.length + 1 ≤ t) (hNzGl : ∀ c ∈ corrGl, c ≠ CommRingOps.zero)
    (PGl : ShamirPadPoly Goldilocks t)
    (corrTw : List (TowerElem k)) (wTw : TowerElem k)
    (hCardTw : corrTw.length + 1 ≤ t) (hNzTw : ∀ c ∈ corrTw, c ≠ CommRingOps.zero)
    (PTw : ShamirPadPoly (TowerElem k) t) :
    let QGl := (shamir_rebalanceEquiv Goldilocks.inv t corrGl wGl hCardGl).toFun PGl
    let QTw := (shamir_rebalanceEquiv (towerInv k) t corrTw wTw hCardTw).toFun PTw
    (add zero (RoundPoly.evalCoeffs QGl.1 zero) = add wGl (RoundPoly.evalCoeffs PGl.1 zero) ∧
     ∀ xc ∈ corrGl, RoundPoly.evalCoeffs QGl.1 xc = RoundPoly.evalCoeffs PGl.1 xc) ∧
    (add zero (RoundPoly.evalCoeffs QTw.1 zero) = add wTw (RoundPoly.evalCoeffs PTw.1 zero) ∧
     ∀ xc ∈ corrTw, RoundPoly.evalCoeffs QTw.1 xc = RoundPoly.evalCoeffs PTw.1 xc) :=
  ⟨pad_bijection_masked_openings_uniform Goldilocks.inv (fun _ hx => Goldilocks.mul_inv_cancel hx) t corrGl wGl hCardGl hNzGl PGl,
   pad_bijection_masked_openings_uniform (towerInv k) (towerMul_inv k) t corrTw wTw hCardTw hNzTw PTw⟩

/-- **`#tooth` Collusion Threshold (`full_collusion_breaks_hiding`)**: with `t` distinct corrupt
    points (one more than the pad bijection tolerates), equal corrupt shares force distinct
    masked openings for distinct secrets, so the openings are no longer hiding. -/
theorem full_collusion_breaks_hiding {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R]
    (t : Nat) (corruptPts : List R)
    (hFull : corruptPts.length = t) (hNodup : corruptPts.Nodup)
    (w₁ w₂ : R) (hDistinct : w₁ ≠ w₂)
    (P Q : ShamirPadPoly R t)
    (hSameShares : ∀ xc ∈ corruptPts, RoundPoly.evalCoeffs P.1 xc = RoundPoly.evalCoeffs Q.1 xc) :
    add w₁ (RoundPoly.evalCoeffs P.1 zero) ≠ add w₂ (RoundPoly.evalCoeffs Q.1 zero) := by
  have hZeroEq : RoundPoly.evalCoeffs P.1 zero = RoundPoly.evalCoeffs Q.1 zero := by
    cases t with
    | zero =>
      have hp0 : P.1 = [] := List.eq_nil_of_length_eq_zero P.2
      have hq0 : Q.1 = [] := List.eq_nil_of_length_eq_zero Q.2
      rw [hp0, hq0]
    | succ d =>
      let diff := polySubFixed P.1 Q.1
      have hDiffLen : diff.length ≤ d + 1 := by
        rw [polySubFixed_length P.1 Q.1 (P.2.trans Q.2.symm), P.2]
        exact Nat.le_refl (d + 1)
      if hAt0 : RoundPoly.evalCoeffs P.1 zero = RoundPoly.evalCoeffs Q.1 zero then
        exact hAt0
      else
        exfalso
        have hNz0 : RoundPoly.evalCoeffs diff zero ≠ zero := by
          rw [evalCoeffs_subFixed P.1 Q.1 zero (P.2.trans Q.2.symm)]
          intro hSub0
          have hAdd := congrArg (fun u => add u (RoundPoly.evalCoeffs Q.1 zero)) hSub0
          rw [sub_add_cancel_right, LawfulCommRing.zero_add] at hAdd
          exact hAt0 hAdd
        have hFiltEq : corruptPts.filter (fun r => decide (RoundPoly.evalCoeffs diff r = zero)) =
            corruptPts := by
          apply List.filter_eq_self.mpr
          intro xc hxc
          rw [evalCoeffs_subFixed P.1 Q.1 xc (P.2.trans Q.2.symm), hSameShares xc hxc,
              LawfulCommRing.sub_self]
          exact decide_eq_true rfl
        have hBound := RoundPoly.roots_nodup_length_le d diff corruptPts hNodup hDiffLen ⟨zero, hNz0⟩
        rw [hFiltEq, hFull] at hBound
        omega
  intro hEqOpen
  rw [hZeroEq] at hEqOpen
  have hSub := congrArg (fun u => sub u (RoundPoly.evalCoeffs Q.1 zero)) hEqOpen
  rw [add_sub_cancel_right, add_sub_cancel_right] at hSub
  exact hDistinct hSub

/-- **`#tooth` Zero Pad (`tooth_unpadded_open_refutes_hiding`)**: an opening masked by the zero
    pad separates any two distinct secrets. -/
theorem tooth_unpadded_open_refutes_hiding {R : Type} [LawfulCommRing R]
    (w₁ w₂ : R) (hDistinct : w₁ ≠ w₂) :
    add w₁ zero ≠ add w₂ zero := by
  rw [LawfulCommRing.add_zero, LawfulCommRing.add_zero]
  exact hDistinct

end PolymorphicPadBijection

/-! ## 3. Vandermonde-at-Zero Reconstruction & Canetti UC Signatures (`idealSig`) -/

structure AbstractSigScheme (PK SK Msg Sig : Type) where
  sign : SK → Msg → Sig
  verify : PK → Msg → Sig → Bool
  complete : PK → SK → Prop
  completeness : ∀ {pk sk}, complete pk sk → ∀ m, verify pk m (sign sk m) = true

inductive UcSigEnv (PK Msg Sig : Type) where
  | halt (verdict : Bool)
  | stepSign (m : Msg) (next : Sig → UcSigEnv PK Msg Sig)
  | stepVerify (m : Msg) (sig : Sig) (next : Bool → UcSigEnv PK Msg Sig)

def execRealSig {PK SK Msg Sig : Type}
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) :
    UcSigEnv PK Msg Sig → Bool
  | .halt b => b
  | .stepSign m next => execRealSig S pk sk (next (S.sign sk m))
  | .stepVerify m sig next => execRealSig S pk sk (next (S.verify pk m sig))

@[expose] def idealSigVerify {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK)
    (recorded : List Msg) (m : Msg) (sig : Sig) : Bool :=
  decide (m ∈ recorded) && S.verify pk m sig

theorem idealSig_unforgeable {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK)
    (recorded : List Msg) (m : Msg) (sig : Sig) (hFresh : m ∉ recorded) :
    idealSigVerify S pk recorded m sig = false := by
  simp [idealSigVerify, hFresh]

/-- **Ideal Signature Execution (`execIdealSig`)**.
`F_SIG` stores only `(pk, recorded)` and answers signing requests through the callback
`simSign : Msg → Sig`. `sk : SK` is not an argument of `execIdealSig`, `findEnvForgery`, or
`signedBeforeForgery`; whether `simSign` itself depends on `sk` is decided by the caller. Every
theorem below that relates this execution to `execRealSig` assumes
`∀ m, simSign m = S.sign sk m`, that is, a signing oracle for the real key. -/
def execIdealSig {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (simSign : Msg → Sig)
    (recorded : List Msg) : UcSigEnv PK Msg Sig → Bool
  | .halt b => b
  | .stepSign m next => execIdealSig S pk simSign (m :: recorded) (next (simSign m))
  | .stepVerify m sig next =>
    execIdealSig S pk simSign recorded (next (idealSigVerify S pk recorded m sig))

def findEnvForgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (simSign : Msg → Sig)
    (recorded : List Msg) : UcSigEnv PK Msg Sig → Option (Msg × Sig)
  | .halt _ => none
  | .stepSign m next => findEnvForgery S pk simSign (m :: recorded) (next (simSign m))
  | .stepVerify m sig next =>
    if m ∉ recorded ∧ S.verify pk m sig = true then
      some (m, sig)
    else
      findEnvForgery S pk simSign recorded (next (idealSigVerify S pk recorded m sig))

theorem execReal_eq_execIdeal_unless_forgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (hSim : ∀ m, simSign m = S.sign sk m)
    (recorded : List Msg) :
    ∀ (Z : UcSigEnv PK Msg Sig),
      findEnvForgery S pk simSign recorded Z = none →
      execRealSig S pk sk Z = execIdealSig S pk simSign recorded Z
  | .halt _, _ => rfl
  | .stepSign m next, hNone => by
    simp only [findEnvForgery] at hNone
    simp only [execRealSig, execIdealSig, ← hSim m]
    exact execReal_eq_execIdeal_unless_forgery S pk sk simSign hSim (m :: recorded) (next (simSign m)) hNone
  | .stepVerify m sig next, hNone => by
    simp only [findEnvForgery] at hNone
    by_cases hBad : m ∉ recorded ∧ S.verify pk m sig = true
    · simp [hBad] at hNone
    · simp only [hBad, ↓reduceIte] at hNone
      have hVerdictEq : S.verify pk m sig = idealSigVerify S pk recorded m sig := by
        unfold idealSigVerify
        by_cases hm : m ∈ recorded
        · simp [hm]
        · cases hv : S.verify pk m sig
          · simp [hm]
          · exact False.elim (hBad ⟨hm, hv⟩)
      simp only [execRealSig, execIdealSig, hVerdictEq]
      exact execReal_eq_execIdeal_unless_forgery S pk sk simSign hSim recorded
        (next (idealSigVerify S pk recorded m sig)) hNone

def signedBeforeForgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (simSign : Msg → Sig)
    (recorded : List Msg) : UcSigEnv PK Msg Sig → List Msg
  | .halt _ => recorded
  | .stepSign m next => signedBeforeForgery S pk simSign (m :: recorded) (next (simSign m))
  | .stepVerify m sig next =>
    if m ∉ recorded ∧ S.verify pk m sig = true then
      recorded
    else
      signedBeforeForgery S pk simSign recorded (next (idealSigVerify S pk recorded m sig))

theorem findEnvForgery_sound {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (simSign : Msg → Sig)
    (recorded : List Msg) :
    ∀ (Z : UcSigEnv PK Msg Sig) {mStar : Msg} {sigStar : Sig},
      findEnvForgery S pk simSign recorded Z = some (mStar, sigStar) →
      mStar ∉ signedBeforeForgery S pk simSign recorded Z ∧ S.verify pk mStar sigStar = true
  | .halt _, _, _, h => by cases h
  | .stepSign m next, _, _, h => by
    simp only [findEnvForgery] at h
    simp only [signedBeforeForgery]
    exact findEnvForgery_sound S pk simSign (m :: recorded) (next (simSign m)) h
  | .stepVerify m sig next, _, _, h => by
    simp only [findEnvForgery] at h
    simp only [signedBeforeForgery]
    by_cases hBad : m ∉ recorded ∧ S.verify pk m sig = true
    · simp only [hBad] at h ⊢
      injection h with hPair
      injection hPair with hm hs
      subst hm hs
      exact hBad
    · simp only [hBad] at h ⊢
      exact findEnvForgery_sound S pk simSign recorded (next (idealSigVerify S pk recorded m sig)) h

@[expose] def UcIndistinguishableOn {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (Z : UcSigEnv PK Msg Sig) : Prop :=
  execRealSig S pk sk Z = execIdealSig S pk simSign [] Z

/-- **Signing-oracle game hop (`sigOracleGameHop_distinguisher_iff_forgery`)**:
assume `hSim : ∀ m, simSign m = S.sign sk m`, so the ideal execution is run with a signing oracle
for the real key. Then (1) any environment on which the real and ideal executions differ contains
a verification query that is a fresh valid forgery `(mStar, sigStar)`, found by `findEnvForgery`;
and (2) conversely any valid pair, submitted as a single verification query, makes the two
executions differ.

This is the "real equals ideal-with-signing-oracle unless forgery" hop. It is not a
UC-realization statement: the ideal side is given the real signer by hypothesis, and no simulator
that lacks `sk` is built here. `tooth_sigOracleGameHop_needs_real_signing_oracle` shows the
hypothesis cannot be dropped. -/
theorem sigOracleGameHop_distinguisher_iff_forgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (hSim : ∀ m, simSign m = S.sign sk m) :
    (∀ Z : UcSigEnv PK Msg Sig,
      ¬ UcIndistinguishableOn S pk sk simSign Z →
      ∃ mStar sigStar,
        findEnvForgery S pk simSign [] Z = some (mStar, sigStar) ∧
        mStar ∉ signedBeforeForgery S pk simSign [] Z ∧
        S.verify pk mStar sigStar = true) ∧
    (∀ mStar sigStar, S.verify pk mStar sigStar = true →
      ¬ UcIndistinguishableOn S pk sk simSign (.stepVerify mStar sigStar (fun b => .halt b))) := by
  refine ⟨?_, ?_⟩
  · intro Z hDist
    cases hFind : findEnvForgery S pk simSign [] Z with
    | none =>
      exact False.elim (hDist (execReal_eq_execIdeal_unless_forgery S pk sk simSign hSim [] Z hFind))
    | some pair =>
      rcases pair with ⟨mStar, sigStar⟩
      obtain ⟨hFresh, hVer⟩ := findEnvForgery_sound S pk simSign [] Z hFind
      exact ⟨mStar, sigStar, rfl, hFresh, hVer⟩
  · intro mStar sigStar hVer hEq
    have hReal : execRealSig S pk sk (.stepVerify mStar sigStar (fun b => .halt b)) = true := by
      simp [execRealSig, hVer]
    have hIdeal : execIdealSig S pk simSign [] (.stepVerify mStar sigStar (fun b => .halt b)) = false := by
      simp [execIdealSig, idealSigVerify]
    have hEq' : execRealSig S pk sk (.stepVerify mStar sigStar (fun b => .halt b)) =
        execIdealSig S pk simSign [] (.stepVerify mStar sigStar (fun b => .halt b)) := hEq
    rw [hReal, hIdeal] at hEq'
    cases hEq'

def execMultiRealSig {PK SK Msg Sig : Type}
    (S_sig : AbstractSigScheme PK SK Msg Sig) : List (PK × SK × UcSigEnv PK Msg Sig) → List Bool
  | [] => []
  | (pk, sk, Z) :: rest => execRealSig S_sig pk sk Z :: execMultiRealSig S_sig rest

/-- Ideal multi-session execution takes only public `(pk, simSign, Z)` triples — ZERO `sk : SK`! -/
def execMultiIdealSig {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S_sig : AbstractSigScheme PK SK Msg Sig) : List (PK × (Msg → Sig) × UcSigEnv PK Msg Sig) → List Bool
  | [] => []
  | (pk, simSign, Z) :: rest => execIdealSig S_sig pk simSign [] Z :: execMultiIdealSig S_sig rest


/-- Finite-family quantitative form of the signing-oracle hop. Verdict advantage is bounded
    by the number of environments where the executed extractor finds a forgery. The oracle
    agreement hypothesis is required at every message, including adaptive signing queries. -/
theorem sigOracleGameHop_advantage_le_extracted_forgeries
    {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (hSim : ∀ m, simSign m = S.sign sk m) (N : Nat)
    (Z : Fin N → UcSigEnv PK Msg Sig) :
    natAbsDiff
      (qsum N (fun i => if execRealSig S pk sk (Z i) then 1 else 0))
      (qsum N (fun i => if execIdealSig S pk simSign [] (Z i) then 1 else 0)) ≤
      qsum N (fun i => if (findEnvForgery S pk simSign [] (Z i)).isSome then 1 else 0) := by
  apply qsum_indicator_diff_le
  intro i hNone
  cases hFind : findEnvForgery S pk simSign [] (Z i) with
  | none => exact execReal_eq_execIdeal_unless_forgery S pk sk simSign hSim [] (Z i) hFind
  | some pair => simp [hFind] at hNone

/-- Telescoping bound for `natAbsDiff`: if consecutive scores differ by at most `eps`, the first
    and the `S`-th differ by at most `S * eps`. A statement about `Nat` sequences only; it mentions
    no protocol. -/
theorem natAbsDiff_telescope (S eps : Nat) (score : Nat → Nat)
    (hStep : ∀ i, i < S → natAbsDiff (score i) (score (i + 1)) ≤ eps) :
    natAbsDiff (score 0) (score S) ≤ S * eps := by
  induction S with
  | zero => simp [natAbsDiff_eq]
  | succ s ih =>
    have ih' := ih (fun i hi => hStep i (Nat.lt_succ_of_lt hi))
    have hLast := hStep s (Nat.lt_succ_self s)
    have hTri := natAbsDiff_triangle (score 0) (score s) (score (s + 1))
    have hLe := Nat.le_trans hTri (Nat.add_le_add ih' hLast)
    rwa [Nat.succ_mul]

/-- **Per-session signing-oracle game hop (`multi_session_uc_realizes`)**: for a list of
    independent sessions, each run with a signing oracle for its own real key
    (`∀ m, simSign m = S_sig.sign sk m`), either every session's real and ideal verdicts agree or
    some session contains a fresh valid forgery. The sessions do not interact; this is
    `sigOracleGameHop_distinguisher_iff_forgery` applied session by session, and inherits its
    signing-oracle hypothesis. -/
theorem multi_session_uc_realizes {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S_sig : AbstractSigScheme PK SK Msg Sig)
    (sessions : List (PK × SK × (Msg → Sig) × UcSigEnv PK Msg Sig))
    (hAllSim : ∀ pk sk simSign Z, (pk, sk, simSign, Z) ∈ sessions →
      ∀ m, simSign m = S_sig.sign sk m) :
    execMultiRealSig S_sig (sessions.map (fun (pk, sk, _, Z) => (pk, sk, Z))) =
      execMultiIdealSig S_sig (sessions.map (fun (pk, _, simSign, Z) => (pk, simSign, Z))) ∨
    ∃ pk sk simSign Z mStar sigStar,
      (pk, sk, simSign, Z) ∈ sessions ∧
      mStar ∉ signedBeforeForgery S_sig pk simSign [] Z ∧
      S_sig.verify pk mStar sigStar = true := by
  induction sessions with
  | nil => exact .inl rfl
  | cons hd rest ih =>
    rcases hd with ⟨pk, sk, simSign, Z⟩
    have hHeadSim : ∀ m, simSign m = S_sig.sign sk m := hAllSim pk sk simSign Z (.head _)
    have hRestSim : ∀ pk' sk' sim' Z', (pk', sk', sim', Z') ∈ rest → ∀ m, sim' m = S_sig.sign sk' m :=
      fun pk' sk' sim' Z' hm => hAllSim pk' sk' sim' Z' (.tail _ hm)
    by_cases hHead : execRealSig S_sig pk sk Z = execIdealSig S_sig pk simSign [] Z
    · rcases ih hRestSim with hRestEq | ⟨pk', sk', sim', Z', mStar, sigStar, hMem, hFresh, hVer⟩
      · exact .inl (by simp [execMultiRealSig, execMultiIdealSig, hHead, hRestEq])
      · exact .inr ⟨pk', sk', sim', Z', mStar, sigStar, .tail _ hMem, hFresh, hVer⟩
    · obtain ⟨mStar, sigStar, _, hFresh, hVer⟩ :=
        (sigOracleGameHop_distinguisher_iff_forgery S_sig pk sk simSign hHeadSim).1 Z hHead
      exact .inr ⟨pk, sk, simSign, Z, mStar, sigStar, .head _, hFresh, hVer⟩

structure CallingProtocol (HighIn HighOut PK Msg Sig : Type) where
  compileEnv : (HighIn → HighOut → Bool) → HighIn → UcSigEnv PK Msg Sig

/-- **Game hop for one compiled caller (`uc_composition_theorem`)**: for the single environment
    `ρ.compileEnv post inp` that a calling protocol compiles to, the real and ideal executions
    agree or the environment contains a fresh valid forgery. This is
    `sigOracleGameHop_distinguisher_iff_forgery` at that environment, under the same
    signing-oracle hypothesis `hSim`; it contains no subroutine-substitution argument and is not
    the universal composition theorem. -/
theorem uc_composition_theorem {HighIn HighOut PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (hSim : ∀ m, simSign m = S.sign sk m)
    (ρ : CallingProtocol HighIn HighOut PK Msg Sig)
    (inp : HighIn) (post : HighIn → HighOut → Bool) :
    let Z := ρ.compileEnv post inp
    execRealSig S pk sk Z = execIdealSig S pk simSign [] Z ∨
    (∃ mStar sigStar,
      mStar ∉ signedBeforeForgery S pk simSign [] Z ∧
      S.verify pk mStar sigStar = true) := by
  intro Z
  by_cases hEq : execRealSig S pk sk Z = execIdealSig S pk simSign [] Z
  · exact .inl hEq
  · obtain ⟨mStar, sigStar, _, hFresh, hVer⟩ :=
      (sigOracleGameHop_distinguisher_iff_forgery S pk sk simSign hSim).1 Z hEq
    exact .inr ⟨mStar, sigStar, hFresh, hVer⟩

/-- Two-message scheme used by the teeth below: every signature is `true` and verification
    returns the signature bit. -/
def toothConstSigScheme : AbstractSigScheme Unit Unit Bool Bool where
  sign := fun _ _ => true
  verify := fun _ _ sig => sig
  complete := fun _ _ => True
  completeness := fun _ _ => rfl

/-- Environment used by the teeth below: request one signature and output it as the verdict. -/
def toothSignThenEchoEnv : UcSigEnv Unit Bool Bool := .stepSign false (fun sig => .halt sig)

/-- **`#tooth` Signing-Oracle Hypothesis (`tooth_sigOracleGameHop_needs_real_signing_oracle`)**:
    with a callback that does not answer as the real signer (`simSign = fun _ => false` against a
    signer that always outputs `true`), the environment that requests one signature and outputs it
    tells the real execution from the ideal one although it makes no verification query, so
    `findEnvForgery` returns `none`. The conclusion of
    `sigOracleGameHop_distinguisher_iff_forgery` fails without `hSim`. -/
theorem tooth_sigOracleGameHop_needs_real_signing_oracle :
    ¬ UcIndistinguishableOn toothConstSigScheme () () (fun _ => false) toothSignThenEchoEnv ∧
    findEnvForgery toothConstSigScheme () (fun _ => false) [] toothSignThenEchoEnv = none := by
  refine ⟨?_, ?_⟩
  · intro h
    have h' : execRealSig toothConstSigScheme () () toothSignThenEchoEnv =
        execIdealSig toothConstSigScheme () (fun _ => false) [] toothSignThenEchoEnv := h
    simp [execRealSig, execIdealSig, toothConstSigScheme, toothSignThenEchoEnv] at h'
  · simp [findEnvForgery, toothSignThenEchoEnv]

/-- **`#tooth` Recorded-Message Gate (`tooth_idealSig_accepts_valid_unsigned_only_in_real`)**:
    a signature that verifies in the real world on a message never sent to the signer is refused
    by the ideal functionality; the recorded-message check is what separates the two worlds. -/
theorem tooth_idealSig_accepts_valid_unsigned_only_in_real {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (m : Msg) (sig : Sig) (hVer : S.verify pk m sig = true) :
    execRealSig S pk sk (.stepVerify m sig (fun b => .halt b)) = true ∧
    execIdealSig S pk simSign [] (.stepVerify m sig (fun b => .halt b)) = false := by
  refine ⟨?_, ?_⟩
  · simp [execRealSig, hVer]
  · simp [execIdealSig, idealSigVerify]

/-- Score sequence that jumps once, from `0` at index `0` to `5` afterwards. -/
def toothJumpScore (i : Nat) : Nat := if i = 0 then 0 else 5

/-- **`#tooth` Per-Step Bound (`tooth_natAbsDiff_telescope_needs_every_step`)**: one unbounded
    step breaks the telescoped bound, so `natAbsDiff_telescope` needs its hypothesis at every
    index. -/

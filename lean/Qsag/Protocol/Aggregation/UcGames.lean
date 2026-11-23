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
   real/ideal difference is a fresh forgery. The explicit `idealTsigSimulator` interacts only through the ideal signing oracle
   and public transcripts. The real-key coupling is isolated in compatibility wrappers;
   this signing-oracle hop alone is not a full threshold UC-realization theorem. Its per-session and per-caller
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

theorem polyAddFixed_cons {R : Type} [CommRingOps R] (a b : R) (as bs : List R) :
    polyAddFixed (a :: as) (b :: bs) = add a b :: polyAddFixed as bs := by rfl

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

/-- Public signing-oracle capability supplied by IdealTsig. The signature is
an oracle response, never a secret-key argument to the simulator. The threshold
and abort policy is implemented by the caller granting this capability. -/
structure IdealTsigSigningOracle (Msg Sig : Type) where
  answer : Msg → Sig

/-- The ideal-world simulator is a closed oracle program. Its only inputs are
public verification, the public key, the public approved-message transcript,
and the environment. In particular neither `SK` nor `AbstractSigScheme.sign`
occurs in its type or implementation. -/
def idealTsigSimulator {PK Msg Sig : Type} [DecidableEq Msg]
    (verify : PK → Msg → Sig → Bool) (pk : PK) (recorded : List Msg) :
    UcSigEnv PK Msg Sig → OracleComp Msg Sig Bool
  | .halt b => .pure b
  | .stepSign m next => .query m (fun sig =>
      idealTsigSimulator verify pk (m :: recorded) (next sig))
  | .stepVerify m sig next => idealTsigSimulator verify pk recorded
      (next (decide (m ∈ recorded) && verify pk m sig))

def execIdealTsigOracle {PK Msg Sig : Type} [DecidableEq Msg]
    (verify : PK → Msg → Sig → Bool) (pk : PK)
    (oracle : IdealTsigSigningOracle Msg Sig) (recorded : List Msg)
    (Z : UcSigEnv PK Msg Sig) : Bool :=
  evalOracleComp oracle.answer (idealTsigSimulator verify pk recorded Z)

/-- Ideal signature execution runs the fixed key-free `idealTsigSimulator`.
`simSign` is the ideal functionality's oracle implementation, supplied only to
`evalOracleComp`; it is not passed as code or state to the simulator. Real-key
agreement is an external oracle coupling used only by the legacy wrappers. -/
def execIdealSig {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (simSign : Msg → Sig)
    (recorded : List Msg) (Z : UcSigEnv PK Msg Sig) : Bool :=
  execIdealTsigOracle S.verify pk ⟨simSign⟩ recorded Z

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

/-- Compatibility with the older callback evaluator. The callback is now
explicitly the ideal functionality's oracle implementation, not a simulator
which may execute arbitrary secret-key computations. -/
theorem idealTsigSimulator_eval {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (oracle : Msg → Sig)
    (recorded : List Msg) (Z : UcSigEnv PK Msg Sig) :
    evalOracleComp oracle (idealTsigSimulator S.verify pk recorded Z) =
      execIdealSig S pk oracle recorded Z := by
  unfold execIdealSig execIdealTsigOracle
  rfl

/-- Public-oracle real execution: all signing is a query to the functionality. -/
def execPublicSig {PK Msg Sig : Type}
    (verify : PK → Msg → Sig → Bool) (pk : PK) (oracle : Msg → Sig) :
    UcSigEnv PK Msg Sig → Bool
  | .halt b => b
  | .stepSign m next => execPublicSig verify pk oracle (next (oracle m))
  | .stepVerify m sig next => execPublicSig verify pk oracle (next (verify pk m sig))

def findPublicForgery {PK Msg Sig : Type} [DecidableEq Msg]
    (verify : PK → Msg → Sig → Bool) (pk : PK) (oracle : Msg → Sig)
    (recorded : List Msg) : UcSigEnv PK Msg Sig → Option (Msg × Sig)
  | .halt _ => none
  | .stepSign m next => findPublicForgery verify pk oracle (m :: recorded) (next (oracle m))
  | .stepVerify m sig next =>
    if m ∉ recorded ∧ verify pk m sig = true then some (m, sig)
    else findPublicForgery verify pk oracle recorded
      (next (decide (m ∈ recorded) && verify pk m sig))

/-- Core oracle simulation theorem: there is no secret key, simulator agreement
hypothesis, or premise asserting the desired conclusion. A difference between
public verification and the ideal recorded-message gate exposes a forgery. -/
theorem idealTsig_oracle_simulation {PK Msg Sig : Type} [DecidableEq Msg]
    (verify : PK → Msg → Sig → Bool) (pk : PK)
    (oracle : IdealTsigSigningOracle Msg Sig) (recorded : List Msg) :
    ∀ Z : UcSigEnv PK Msg Sig,
      findPublicForgery verify pk oracle.answer recorded Z = none →
      execPublicSig verify pk oracle.answer Z = execIdealTsigOracle verify pk oracle recorded Z
  | .halt _, _ => rfl
  | .stepSign m next, hn => by
    exact idealTsig_oracle_simulation verify pk oracle (m :: recorded) (next (oracle.answer m)) hn
  | .stepVerify m sig next, hn => by
    simp only [findPublicForgery] at hn
    by_cases hb : m ∉ recorded ∧ verify pk m sig = true
    · simp [hb] at hn
    · simp only [hb, ↓reduceIte] at hn
      have hv : verify pk m sig = (decide (m ∈ recorded) && verify pk m sig) := by
        by_cases hm : m ∈ recorded
        · simp [hm]
        · cases he : verify pk m sig
          · simp [hm]
          · exact False.elim (hb ⟨hm, he⟩)
      change execPublicSig verify pk oracle.answer (next (verify pk m sig)) = _
      rw [hv]
      exact idealTsig_oracle_simulation verify pk oracle recorded _ hn

theorem execPublicSig_real {PK SK Msg Sig : Type}
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (Z : UcSigEnv PK Msg Sig) :
    execPublicSig S.verify pk (S.sign sk) Z = execRealSig S pk sk Z := by
  induction Z with
  | halt b => rfl
  | stepSign m next ih => exact ih (S.sign sk m)
  | stepVerify m sig next ih => exact ih (S.verify pk m sig)

theorem findPublicForgery_eq {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (oracle : Msg → Sig)
    (recorded : List Msg) (Z : UcSigEnv PK Msg Sig) :
    findPublicForgery S.verify pk oracle recorded Z = findEnvForgery S pk oracle recorded Z := by
  induction Z generalizing recorded with
  | halt b => rfl
  | stepSign m next ih => exact ih (oracle m) (m :: recorded)
  | stepVerify m sig next ih =>
    simp only [findPublicForgery, findEnvForgery]
    split
    · rfl
    · exact ih (idealSigVerify S pk recorded m sig) recorded

/-- Legacy real-key coupling wrapper. `hOracle` relates the functionality's
oracle to the real-world signer; the simulator itself is `idealTsigSimulator`,
whose definition above cannot access the real key. -/
theorem execReal_eq_execIdeal_unless_forgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (hOracle : ∀ m, simSign m = S.sign sk m)
    (recorded : List Msg) :
    ∀ (Z : UcSigEnv PK Msg Sig),
      findEnvForgery S pk simSign recorded Z = none →
      execRealSig S pk sk Z = execIdealSig S pk simSign recorded Z
  | Z, hNone => by
    have h := idealTsig_oracle_simulation S.verify pk ⟨simSign⟩ recorded Z
      (by rwa [findPublicForgery_eq])
    change execPublicSig S.verify pk simSign Z =
      evalOracleComp simSign (idealTsigSimulator S.verify pk recorded Z) at h
    rw [idealTsigSimulator_eval] at h
    have ho : simSign = S.sign sk := funext hOracle
    rw [ho, execPublicSig_real] at h
    simpa only [ho] using h

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
assume `hOracle : ∀ m, simSign m = S.sign sk m`, so the ideal execution is run with a signing oracle
for the real key. Then (1) any environment on which the real and ideal executions differ contains
a verification query that is a fresh valid forgery `(mStar, sigStar)`, found by `findEnvForgery`;
and (2) conversely any valid pair, submitted as a single verification query, makes the two
executions differ.

This is the "real equals ideal-with-signing-oracle unless forgery" hop. It is not a
UC-realization statement: the ideal signing functionality must still be coupled to the
real signer. The simulator is the key-free oracle program `idealTsigSimulator`. `tooth_sigOracleGameHop_needs_real_signing_oracle` shows the
hypothesis cannot be dropped. -/
theorem sigOracleGameHop_distinguisher_iff_forgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (hOracle : ∀ m, simSign m = S.sign sk m) :
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
      exact False.elim (hDist (execReal_eq_execIdeal_unless_forgery S pk sk simSign hOracle [] Z hFind))
    | some pair =>
      rcases pair with ⟨mStar, sigStar⟩
      obtain ⟨hFresh, hVer⟩ := findEnvForgery_sound S pk simSign [] Z hFind
      exact ⟨mStar, sigStar, rfl, hFresh, hVer⟩
  · intro mStar sigStar hVer hEq
    have hReal : execRealSig S pk sk (.stepVerify mStar sigStar (fun b => .halt b)) = true := by
      simp [execRealSig, hVer]
    have hIdeal : execIdealSig S pk simSign [] (.stepVerify mStar sigStar (fun b => .halt b)) = false := by
      simp [execIdealSig, execIdealTsigOracle, idealTsigSimulator, evalOracleComp]
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
    (hOracle : ∀ m, simSign m = S.sign sk m) (N : Nat)
    (Z : Fin N → UcSigEnv PK Msg Sig) :
    natAbsDiff
      (qsum N (fun i => if execRealSig S pk sk (Z i) then 1 else 0))
      (qsum N (fun i => if execIdealSig S pk simSign [] (Z i) then 1 else 0)) ≤
      qsum N (fun i => if (findEnvForgery S pk simSign [] (Z i)).isSome then 1 else 0) := by
  apply qsum_indicator_diff_le
  intro i hNone
  cases hFind : findEnvForgery S pk simSign [] (Z i) with
  | none => exact execReal_eq_execIdeal_unless_forgery S pk sk simSign hOracle [] (Z i) hFind
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
    (hAllOracle : ∀ pk sk simSign Z, (pk, sk, simSign, Z) ∈ sessions →
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
    have hHeadOracle : ∀ m, simSign m = S_sig.sign sk m := hAllOracle pk sk simSign Z (.head _)
    have hRestOracle : ∀ pk' sk' sim' Z', (pk', sk', sim', Z') ∈ rest → ∀ m, sim' m = S_sig.sign sk' m :=
      fun pk' sk' sim' Z' hm => hAllOracle pk' sk' sim' Z' (.tail _ hm)
    by_cases hHead : execRealSig S_sig pk sk Z = execIdealSig S_sig pk simSign [] Z
    · rcases ih hRestOracle with hRestEq | ⟨pk', sk', sim', Z', mStar, sigStar, hMem, hFresh, hVer⟩
      · exact .inl (by simp [execMultiRealSig, execMultiIdealSig, hHead, hRestEq])
      · exact .inr ⟨pk', sk', sim', Z', mStar, sigStar, .tail _ hMem, hFresh, hVer⟩
    · obtain ⟨mStar, sigStar, _, hFresh, hVer⟩ :=
        (sigOracleGameHop_distinguisher_iff_forgery S_sig pk sk simSign hHeadOracle).1 Z hHead
      exact .inr ⟨pk, sk, simSign, Z, mStar, sigStar, .head _, hFresh, hVer⟩

structure CallingProtocol (HighIn HighOut PK Msg Sig : Type) where
  compileEnv : (HighIn → HighOut → Bool) → HighIn → UcSigEnv PK Msg Sig

/-- **Game hop for one compiled caller (`uc_composition_theorem`)**: for the single environment
    `ρ.compileEnv post inp` that a calling protocol compiles to, the real and ideal executions
    agree or the environment contains a fresh valid forgery. This is
    `sigOracleGameHop_distinguisher_iff_forgery` at that environment, under the same
    signing-oracle hypothesis `hOracle`; it contains no subroutine-substitution argument and is not
    the universal composition theorem. -/
theorem uc_composition_theorem {HighIn HighOut PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (hOracle : ∀ m, simSign m = S.sign sk m)
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
      (sigOracleGameHop_distinguisher_iff_forgery S pk sk simSign hOracle).1 Z hEq
    exact .inr ⟨mStar, sigStar, hFresh, hVer⟩

/-- Key- and message-tagged `AbstractSigScheme` over `UInt8`: `sign sk m = (sk ^^^ 0xA5, (sk ^^^ 0xA5) ^^^ m)`
    and `verify pk m sig` checks both `sig.1 = pk` and `sig.2 = pk ^^^ m`. -/
def keyedTagSigScheme : AbstractSigScheme UInt8 UInt8 UInt8 (UInt8 × UInt8) where
  sign := fun sk m => (sk ^^^ 0xA5, (sk ^^^ 0xA5) ^^^ m)
  verify := fun pk m sig => decide (sig.1 = pk ∧ sig.2 = pk ^^^ m)
  complete := fun pk sk => pk = sk ^^^ 0xA5
  completeness := fun h _ => by subst h; exact decide_eq_true ⟨rfl, rfl⟩

/-- Environment requesting a signature on `m = 0x42` and checking that its message-tag byte matches `0xA5 ^^^ 0x42`. -/
def keyedSignCheckTagEnv : UcSigEnv UInt8 UInt8 (UInt8 × UInt8) :=
  .stepSign 0x42 (fun sig => .halt (decide (sig.2 = (0xA5 ^^^ 0x42))))

/-- **`#tooth` Signing-Oracle Hypothesis (`tooth_sigOracleGameHop_needs_real_signing_oracle`)**:
    when `simSign` drops key-masking on the tag (`simSign m := (0xA5, m)` instead of `(0xA5, 0xA5 ^^^ m)`),
    `keyedSignCheckTagEnv` distinguishes real from ideal (`true ≠ false`) with zero verification
    queries (`findEnvForgery = none`), showing `hOracle` is load-bearing in
    `sigOracleGameHop_distinguisher_iff_forgery`. -/
theorem tooth_sigOracleGameHop_needs_real_signing_oracle :
    ¬ UcIndistinguishableOn keyedTagSigScheme 0xA5 0 (fun m => (0xA5, m)) keyedSignCheckTagEnv ∧
    findEnvForgery keyedTagSigScheme 0xA5 (fun m => (0xA5, m)) [] keyedSignCheckTagEnv = none := by
  refine ⟨?_, ?_⟩
  · intro h
    have h' : execRealSig keyedTagSigScheme 0xA5 0 keyedSignCheckTagEnv =
        execIdealSig keyedTagSigScheme 0xA5 (fun m => (0xA5, m)) [] keyedSignCheckTagEnv := h
    revert h'
    decide
  · rfl

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
  · simp [execIdealSig, execIdealTsigOracle, idealTsigSimulator, evalOracleComp]

/-- Score sequence that jumps once, from `0` at index `0` to `5` afterwards. -/
def toothJumpScore (i : Nat) : Nat := if i = 0 then 0 else 5

/-- **`#tooth` Per-Step Bound (`tooth_natAbsDiff_telescope_needs_every_step`)**: one unbounded
    step breaks the telescoped bound, so `natAbsDiff_telescope` needs its hypothesis at every
    index. -/
theorem tooth_natAbsDiff_telescope_needs_every_step :
    (∀ i, 1 ≤ i → i < 2 → natAbsDiff (toothJumpScore i) (toothJumpScore (i + 1)) ≤ 1) ∧
    ¬ (natAbsDiff (toothJumpScore 0) (toothJumpScore 2) ≤ 2 * 1) := by
  refine ⟨?_, by rw [natAbsDiff_eq]; decide⟩
  intro i h1 h2
  have hi : i = 1 := by omega
  subst hi
  rw [natAbsDiff_eq]
  decide

/-! ## 4. Finite Sample Spaces: Fubini, Bijection Invariance, Preprocessing-Generator Games -/

/-- Number of accepting sample pairs of a Boolean experiment `X` over two independent uniformly
    indexed sample spaces (`Ca * Cb` pairs in total). -/
@[expose] def acceptPairs {A B : Type} (Ca Cb : Nat) (sa : Fin Ca → A) (sb : Fin Cb → B)
    (X : A → B → Bool) : Nat :=
  qsum Ca (fun i => qsum Cb (fun j => if X (sa i) (sb j) then 1 else 0))

/-- Generator-indistinguishability game. `gen` maps a uniform seed in `Fin Cg` to a sample; `unif`
    indexes the reference sample space; `B x` is the number of internal coin values on which the
    (randomised) distinguisher accepts `x`. The value is the advantage numerator
    `|Pr[B(gen s)] - Pr[B(unif u)]|` cleared of the two sample-space sizes `Cg` and `Cu`. -/
@[expose] def samplerAdvNum {X : Type} (Cg Cu : Nat) (gen : Fin Cg → X) (unif : Fin Cu → X)
    (B : X → Nat) : Nat :=
  natAbsDiff (qsum Cg (fun s => B (gen s)) * Cu) (qsum Cu (fun u => B (unif u)) * Cg)

/-- PRG game for an experiment `X`: the reduction replaces the pad tape expanded from a seed by
    `prg` with a uniform tape, drawing the second component from `ot` itself. -/
@[expose] def prgReductionAdvNum {T K : Type} (Cs Ct Co : Nat) (prg : Fin Cs → T)
    (unifT : Fin Ct → T) (ot : Fin Co → K) (X : T → K → Bool) : Nat :=
  samplerAdvNum Cs Ct prg unifT (fun τ => qsum Co (fun o => if X τ (ot o) then 1 else 0))

/-- Correlated-key (OT) game for an experiment `X`: the reduction replaces the key produced by the
    correlation generator `ot` with a uniform key, drawing the tape uniformly itself. -/
@[expose] def otReductionAdvNum {T K : Type} (Ct Co CK : Nat) (unifT : Fin Ct → T)
    (ot : Fin Co → K) (unifK : Fin CK → K) (X : T → K → Bool) : Nat :=
  samplerAdvNum Co CK ot unifK (fun κ => qsum Ct (fun i => if X (unifT i) κ then 1 else 0))

theorem samplerAdvNum_self {X : Type} (C : Nat) (gen : Fin C → X) (B : X → Nat) :
    samplerAdvNum C C gen gen B = 0 := by
  unfold samplerAdvNum
  rw [natAbsDiff_eq]
  split <;> omega

/-- The game is not vacuous: a constant generator is told apart from a two-point space. -/
theorem samplerAdvNum_constant_generator_detected :
    samplerAdvNum 1 2 (fun _ => false) (fun i => decide (i.val = 1)) (fun b => if b then 1 else 0) = 1 := by
  simp [samplerAdvNum, qsum_succ, qsum_zero, natAbsDiff_eq]

private theorem natAbsDiff_three_hop (N0 N1 N2 N3 Cs Co Ct CK G : Nat)
    (h : natAbsDiff N2 N3 ≤ G) :
    natAbsDiff (N0 * (Ct * CK)) (N3 * (Cs * Co)) ≤
      Cs * Co * G + CK * natAbsDiff (N0 * Ct) (N1 * Cs) + Cs * natAbsDiff (N1 * CK) (N2 * Co) := by
  have e0 : N0 * (Ct * CK) = CK * (N0 * Ct) := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  have e1 : CK * (N1 * Cs) = Cs * (N1 * CK) := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  have e2 : Cs * (N2 * Co) = Cs * Co * N2 := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  have e3 : N3 * (Cs * Co) = Cs * Co * N3 := by
    simp only [Nat.mul_comm]
  have hA : natAbsDiff (CK * (N0 * Ct)) (CK * (N1 * Cs)) = CK * natAbsDiff (N0 * Ct) (N1 * Cs) :=
    natAbsDiff_mul_left _ _ _
  have hB : natAbsDiff (CK * (N1 * Cs)) (Cs * Co * N2) = Cs * natAbsDiff (N1 * CK) (N2 * Co) := by
    rw [e1, ← e2]
    exact natAbsDiff_mul_left _ _ _
  have hC : natAbsDiff (Cs * Co * N2) (Cs * Co * N3) ≤ Cs * Co * G := by
    rw [natAbsDiff_mul_left]
    exact Nat.mul_le_mul_left _ h
  have t1 := natAbsDiff_triangle (CK * (N0 * Ct)) (CK * (N1 * Cs)) (Cs * Co * N3)
  have t2 := natAbsDiff_triangle (CK * (N1 * Cs)) (Cs * Co * N2) (Cs * Co * N3)
  rw [hA] at t1
  rw [hB] at t2
  rw [e0, e3]
  omega

/-- **Simulation-up-to-Bad Counting Hop (`acceptPairs_gap_of_bijection`)**: if a tape bijection
    `e` makes experiment `X` on `τ` equal to experiment `Y` on `e τ` outside a bad event, and for
    every tape at most `q` keys are bad, then over uniform tape and key the two experiments differ
    on at most `Ct * q` sample pairs. -/
theorem acceptPairs_gap_of_bijection {T K : Type} {Ct CK : Nat}
    (enumT : SimpleEquiv (Fin Ct) T) (e : SimpleEquiv T T) (unifK : Fin CK → K)
    (X Y : T → K → Bool) (bad : T → K → Bool) (q : Nat)
    (hAgree : ∀ τ κ, bad τ κ = false → X τ κ = Y (e.toFun τ) κ)
    (hBad : ∀ τ, qsum CK (fun j => if bad τ (unifK j) then 1 else 0) ≤ q) :
    natAbsDiff (acceptPairs Ct CK enumT.toFun unifK X) (acceptPairs Ct CK enumT.toFun unifK Y) ≤
      Ct * q := by
  have hInv := qsum_bijection_invariant enumT e
    (fun τ => qsum CK (fun j => if Y τ (unifK j) then 1 else 0))
  have hPt : ∀ i : Fin Ct,
      natAbsDiff (qsum CK (fun j => if X (enumT.toFun i) (unifK j) then 1 else 0))
                 (qsum CK (fun j => if Y (e.toFun (enumT.toFun i)) (unifK j) then 1 else 0)) ≤ q :=
    fun i => Nat.le_trans
      (qsum_indicator_diff_le (fun j => X (enumT.toFun i) (unifK j))
        (fun j => Y (e.toFun (enumT.toFun i)) (unifK j))
        (fun j => bad (enumT.toFun i) (unifK j)) (fun j hj => hAgree _ _ hj))
      (hBad (enumT.toFun i))
  have hSum := natAbsDiff_qsum_le
    (fun i : Fin Ct => qsum CK (fun j => if X (enumT.toFun i) (unifK j) then 1 else 0))
    (fun i : Fin Ct => qsum CK (fun j => if Y (e.toFun (enumT.toFun i)) (unifK j) then 1 else 0))
  have hBound := qsum_le_qsum (g := fun _ : Fin Ct => q) hPt
  rw [qsum_const] at hBound
  rw [hInv] at hSum
  exact Nat.le_trans hSum hBound

/-- **Preprocessing Hybrid Reduction (`preprocessing_hybrid_bound`)**: let `X` be the real
    experiment and `Y` the ideal one. If over uniform tape and uniform key they differ on at most
    `G` sample pairs, then running `X` on `prg`-expanded tapes and `ot`-generated keys differs from
    `Y` on uniform samples by at most the uniform gap plus the advantages of the two explicit
    reduction distinguishers, all over the common denominator `Cs * Co * Ct * CK`. -/
theorem preprocessing_hybrid_bound {T K : Type} (Cs Ct Co CK : Nat)
    (prg : Fin Cs → T) (unifT : Fin Ct → T) (ot : Fin Co → K) (unifK : Fin CK → K)
    (X Y : T → K → Bool) (G : Nat)
    (hGap : natAbsDiff (acceptPairs Ct CK unifT unifK X) (acceptPairs Ct CK unifT unifK Y) ≤ G) :
    natAbsDiff (acceptPairs Cs Co prg ot X * (Ct * CK))
               (acceptPairs Ct CK unifT unifK Y * (Cs * Co)) ≤
      Cs * Co * G
        + CK * prgReductionAdvNum Cs Ct Co prg unifT ot X
        + Cs * otReductionAdvNum Ct Co CK unifT ot unifK X := by
  have hOt1 : qsum Co (fun o => qsum Ct (fun i => if X (unifT i) (ot o) then 1 else 0)) =
      acceptPairs Ct Co unifT ot X :=
    qsum_comm _ _ (fun (o : Fin Co) (i : Fin Ct) => if X (unifT i) (ot o) then 1 else 0)
  have hOt2 : qsum CK (fun u => qsum Ct (fun i => if X (unifT i) (unifK u) then 1 else 0)) =
      acceptPairs Ct CK unifT unifK X :=
    qsum_comm _ _ (fun (u : Fin CK) (i : Fin Ct) => if X (unifT i) (unifK u) then 1 else 0)
  have hPrg : prgReductionAdvNum Cs Ct Co prg unifT ot X =
      natAbsDiff (acceptPairs Cs Co prg ot X * Ct) (acceptPairs Ct Co unifT ot X * Cs) := rfl
  have hOt : otReductionAdvNum Ct Co CK unifT ot unifK X =
      natAbsDiff (acceptPairs Ct Co unifT ot X * CK) (acceptPairs Ct CK unifT unifK X * Co) := by
    show natAbsDiff
        (qsum Co (fun o => qsum Ct (fun i => if X (unifT i) (ot o) then 1 else 0)) * CK)
        (qsum CK (fun u => qsum Ct (fun i => if X (unifT i) (unifK u) then 1 else 0)) * Co) = _
    rw [hOt1, hOt2]
  rw [hPrg, hOt]
  exact natAbsDiff_three_hop _ _ _ _ Cs Co Ct CK G hGap

/-- Break witness: an advantage above the uniform gap forces one of the two generator games to
    have non-zero advantage for the explicit reduction distinguisher. -/
theorem preprocessing_break_witness {T K : Type} (Cs Ct Co CK : Nat)
    (prg : Fin Cs → T) (unifT : Fin Ct → T) (ot : Fin Co → K) (unifK : Fin CK → K)
    (X Y : T → K → Bool) (G : Nat)
    (hGap : natAbsDiff (acceptPairs Ct CK unifT unifK X) (acceptPairs Ct CK unifT unifK Y) ≤ G)
    (hDist : Cs * Co * G < natAbsDiff (acceptPairs Cs Co prg ot X * (Ct * CK))
                                       (acceptPairs Ct CK unifT unifK Y * (Cs * Co))) :
    0 < prgReductionAdvNum Cs Ct Co prg unifT ot X ∨
    0 < otReductionAdvNum Ct Co CK unifT ot unifK X := by
  have hB := preprocessing_hybrid_bound Cs Ct Co CK prg unifT ot unifK X Y G hGap
  cases hp : prgReductionAdvNum Cs Ct Co prg unifT ot X with
  | succ a => exact .inl (Nat.succ_pos a)
  | zero =>
    cases ho : otReductionAdvNum Ct Co CK unifT ot unifK X with
    | succ b => exact .inr (Nat.succ_pos b)
    | zero =>
      rw [hp, ho, Nat.mul_zero, Nat.mul_zero] at hB
      exact absurd hDist (Nat.not_lt.mpr hB)

/-! ## 5. Shamir Share / Pad Rebalancing for Masked Openings -/

section ShareRebalance
open CommRingOps

theorem vanishCorruptUnit0_length {R : Type} [CommRingOps R] (inv : R → R) (t : Nat)
    (corruptPts : List R) (hCard : corruptPts.length + 1 ≤ t) :
    (vanishCorruptUnit0 inv t corruptPts).length = t := by
  unfold vanishCorruptUnit0
  dsimp only
  rw [List.length_append, List.length_replicate, vanishCorruptRaw_length]
  omega

private theorem sub_add_add_cancel_left {R : Type} [LawfulCommRing R] (w p q : R) :
    sub (add w p) (add w q) = sub p q := by
  have h : add w p = add (sub p q) (add w q) := by
    rw [LawfulCommRing.add_comm w q, ← LawfulCommRing.add_assoc, sub_add_cancel_right,
        LawfulCommRing.add_comm]
  rw [h, add_sub_cancel_right]

/-- Bijection on the sharing randomness of a degree-`d` Shamir sharing `w :: A` that turns a
    sharing of `w` into a sharing of `zero` with the same shares at every corrupt point. -/
def shamirShare_rebalanceEquiv {R : Type} [LawfulCommRing R]
    (inv : R → R) (d : Nat) (corruptPts : List R)
    (w : R) (hCard : corruptPts.length + 1 ≤ d + 1) :
    SimpleEquiv (ShamirPadPoly R d) (ShamirPadPoly R d) :=
  let delta := polyScale w (vanishCorruptUnit0 inv (d + 1) corruptPts).tail
  have hDeltaLen : delta.length = d := by
    rw [polyScale_length, List.length_tail, vanishCorruptUnit0_length inv (d + 1) corruptPts hCard]
    exact Nat.add_sub_cancel d 1
  { toFun := fun ⟨p, hp⟩ => ⟨polySubFixed p delta, by rw [polySubFixed_length p delta (hp.trans hDeltaLen.symm), hp]⟩
    invFun := fun ⟨q, hq⟩ => ⟨polyAddFixed q delta, by rw [polyAddFixed_length q delta (hq.trans hDeltaLen.symm), hq]⟩
    left_inv := fun ⟨p, hp⟩ => Subtype.ext (polyAdd_polySub_cancel p delta (hp.trans hDeltaLen.symm))
    right_inv := fun ⟨q, hq⟩ => Subtype.ext (polySub_polyAdd_cancel q delta (hq.trans hDeltaLen.symm)) }

/-- **Masked-Opening Rebalancing (`shamir_share_pad_rebalance`)**: for a secret `w` shared by the
    standard polynomial `w :: A` and masked by the pad polynomial `P`, moving `A` and `P` through
    the two bijections yields a sharing `zero :: A'` of `zero` and a pad `P'` such that every
    corrupt party's share and pad share are unchanged and the masked polynomial `(w :: A) + P`
    takes the same value at every point (so every broadcast masked share is unchanged). -/
theorem shamir_share_pad_rebalance {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (d : Nat) (corruptPts : List R) (w : R)
    (hCard : corruptPts.length + 1 ≤ d + 1)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero)
    (A : ShamirPadPoly R d) (P : ShamirPadPoly R (d + 1)) :
    let A' := (shamirShare_rebalanceEquiv inv d corruptPts w hCard).toFun A
    let P' := (shamir_rebalanceEquiv inv (d + 1) corruptPts w hCard).toFun P
    (∀ xc ∈ corruptPts,
      RoundPoly.evalCoeffs (zero :: A'.1) xc = RoundPoly.evalCoeffs (w :: A.1) xc) ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs P'.1 xc = RoundPoly.evalCoeffs P.1 xc) ∧
    (∀ x : R,
      add (RoundPoly.evalCoeffs (zero :: A'.1) x) (RoundPoly.evalCoeffs P'.1 x) =
        add (RoundPoly.evalCoeffs (w :: A.1) x) (RoundPoly.evalCoeffs P.1 x)) := by
  intro A' P'
  obtain ⟨hULen, hU0, hUCorr⟩ := vanishCorruptUnit0_props inv hInv hCard hNonZero
  obtain ⟨_, hPadShares⟩ :=
    pad_bijection_masked_openings_uniform inv hInv (d + 1) corruptPts w hCard hNonZero P
  have hScaleLen : (polyScale w (vanishCorruptUnit0 inv (d + 1) corruptPts)).length = d + 1 := by
    rw [polyScale_length, hULen]
  have hP' : ∀ x : R, RoundPoly.evalCoeffs P'.1 x =
      add (RoundPoly.evalCoeffs P.1 x)
          (mul w (RoundPoly.evalCoeffs (vanishCorruptUnit0 inv (d + 1) corruptPts) x)) := by
    intro x
    change RoundPoly.evalCoeffs
      (polyAddFixed P.1 (polyScale w (vanishCorruptUnit0 inv (d + 1) corruptPts))) x = _
    rw [evalCoeffs_addFixed P.1 _ _ (P.2.trans hScaleLen.symm), evalCoeffs_scale]
  have hUCons : vanishCorruptUnit0 inv (d + 1) corruptPts =
      one :: (vanishCorruptUnit0 inv (d + 1) corruptPts).tail := by
    cases hU : vanishCorruptUnit0 inv (d + 1) corruptPts with
    | nil =>
      rw [hU] at hULen
      exact absurd hULen (Nat.succ_ne_zero d).symm
    | cons c cs =>
      rw [hU] at hU0
      have hc : c = one := by
        simpa only [RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
          using hU0
      rw [hc]
      rfl
  have hTailLen : (vanishCorruptUnit0 inv (d + 1) corruptPts).tail.length = d := by
    rw [List.length_tail, hULen]
    exact Nat.add_sub_cancel d 1
  have hA' : ∀ x : R, RoundPoly.evalCoeffs (zero :: A'.1) x =
      sub (RoundPoly.evalCoeffs (w :: A.1) x)
          (mul w (RoundPoly.evalCoeffs (vanishCorruptUnit0 inv (d + 1) corruptPts) x)) := by
    intro x
    have hEvalU : RoundPoly.evalCoeffs (vanishCorruptUnit0 inv (d + 1) corruptPts) x =
        add one (mul x (RoundPoly.evalCoeffs (vanishCorruptUnit0 inv (d + 1) corruptPts).tail x)) :=
      congrArg (fun l => RoundPoly.evalCoeffs l x) hUCons
    have hLenEq : A.1.length =
        (polyScale w (vanishCorruptUnit0 inv (d + 1) corruptPts).tail).length := by
      rw [polyScale_length, hTailLen, A.2]
    change RoundPoly.evalCoeffs
      (zero :: polySubFixed A.1 (polyScale w (vanishCorruptUnit0 inv (d + 1) corruptPts).tail)) x = _
    rw [hEvalU]
    simp only [RoundPoly.evalCoeffs_cons]
    rw [evalCoeffs_subFixed A.1 _ x hLenEq, evalCoeffs_scale, LawfulCommRing.zero_add,
        LawfulCommRing.mul_sub, LawfulCommRing.left_distrib w, LawfulCommRing.mul_one,
        sub_add_add_cancel_left, ← LawfulCommRing.mul_assoc x w, LawfulCommRing.mul_comm x w,
        LawfulCommRing.mul_assoc w x]
  refine ⟨?_, hPadShares, ?_⟩
  · intro xc hxc
    rw [hA' xc, hUCorr xc hxc, LawfulCommRing.mul_zero, LawfulCommRing.sub_zero]
  · intro x
    rw [hA' x, hP' x, LawfulCommRing.add_comm (RoundPoly.evalCoeffs P.1 x),
        ← LawfulCommRing.add_assoc, sub_add_cancel_right]

/-- Inhabitedness over `GF(4)`: degree bound `d = 1`, one corrupt point, a non-zero secret. -/
theorem shamir_share_pad_rebalance_gf4
    (A : ShamirPadPoly (TowerElem 1) 1) (P : ShamirPadPoly (TowerElem 1) 2) :
    let A' := (shamirShare_rebalanceEquiv (towerInv 1) 1 [(towerOne 1)]
      (towerOne 1) (by decide)).toFun A
    let P' := (shamir_rebalanceEquiv (towerInv 1) 2 [(towerOne 1)]
      (towerOne 1) (by decide)).toFun P
    RoundPoly.evalCoeffs (zero :: A'.1) (towerOne 1) =
      RoundPoly.evalCoeffs ((towerOne 1) :: A.1) (towerOne 1) ∧
    RoundPoly.evalCoeffs P'.1 (towerOne 1) =
      RoundPoly.evalCoeffs P.1 (towerOne 1) ∧
    (∀ x : TowerElem 1,
      add (RoundPoly.evalCoeffs (zero :: A'.1) x) (RoundPoly.evalCoeffs P'.1 x) =
        add (RoundPoly.evalCoeffs ((towerOne 1) :: A.1) x)
            (RoundPoly.evalCoeffs P.1 x)) := by
  intro A' P'
  have hNz : ∀ c ∈ [(towerOne 1)], c ≠ (zero : TowerElem 1) := by
    intro c hc
    rw [List.mem_singleton.mp hc]
    decide
  obtain ⟨h1, h2, h3⟩ :=
    shamir_share_pad_rebalance (towerInv 1) (towerMul_inv 1) 1 [(towerOne 1)]
      (towerOne 1) (by decide) hNz A P
  exact ⟨h1 _ (.head _), h2 _ (.head _), h3⟩

end ShareRebalance

/-! ## 6. Multi-Session Product-Tape Bijections & Concurrent Hybrid Game Combinator -/

/-- Constructive pairing `Fin A × Fin B → Fin (A * B)`. -/
def ucPairFin {A B : Nat} (a : Fin A) (b : Fin B) : Fin (A * B) :=
  ⟨a.val * B + b.val, by
    have h1 : (a.val + 1) * B ≤ A * B := Nat.mul_le_mul_right B a.isLt
    rw [Nat.add_mul, Nat.one_mul] at h1
    have h2 : b.val < B := b.isLt
    omega⟩

/-- Left quotient projection `Fin (A * B) → Fin A` (`0 < B`). -/
def ucSplitLeft {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) : Fin A :=
  ⟨x.val / B, (Nat.div_lt_iff_lt_mul hB).mpr x.isLt⟩

/-- Right remainder projection `Fin (A * B) → Fin B` (`0 < B`). -/
def ucSplitRight {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) : Fin B :=
  ⟨x.val % B, Nat.mod_lt x.val hB⟩

theorem ucPair_split {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) :
    ucPairFin (ucSplitLeft hB x) (ucSplitRight hB x) = x := by
  apply Fin.ext
  dsimp [ucPairFin, ucSplitLeft, ucSplitRight]
  have h := Nat.div_add_mod x.val B
  rw [Nat.mul_comm B (x.val / B)] at h
  exact h

theorem ucSplitLeft_pair {A B : Nat} (hB : 0 < B) (a : Fin A) (b : Fin B) :
    ucSplitLeft hB (ucPairFin a b) = a := by
  apply Fin.ext
  dsimp [ucSplitLeft, ucPairFin]
  rw [Nat.mul_comm a.val B, Nat.mul_add_div hB, Nat.div_eq_of_lt b.isLt, Nat.add_zero]

theorem ucSplitRight_pair {A B : Nat} (hB : 0 < B) (a : Fin A) (b : Fin B) :
    ucSplitRight hB (ucPairFin a b) = b := by
  apply Fin.ext
  dsimp [ucSplitRight, ucPairFin]
  rw [Nat.mul_comm a.val B, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]

private theorem uc_qsum_snoc : ∀ (k : Nat) (g : Nat → Nat),
    qsum (k + 1) (fun i => g i.val) = qsum k (fun i => g i.val) + g k
  | 0, g => by simp [qsum_zero, qsum_succ]
  | k + 1, g => by
    conv => lhs; rw [qsum_succ]
    dsimp only
    rw [uc_qsum_snoc k (fun j => g (j + 1))]
    conv => rhs; rw [qsum_succ]
    dsimp only
    omega

private theorem uc_qsum_nat_eq_of_eq {m n : Nat} (h : m = n) (g : Nat → Nat) :
    qsum m (fun i => g i.val) = qsum n (fun i => g i.val) := by
  subst h; rfl

private theorem uc_qsum_nat_add_split (m : Nat) : ∀ (n : Nat) (g : Nat → Nat),
    qsum (m + n) (fun i => g i.val) =
      qsum m (fun i => g i.val) + qsum n (fun j => g (m + j.val))
  | 0, g => by
    simp [qsum_zero]
  | n + 1, g => by
    have hStep : m + (n + 1) = (m + n) + 1 := rfl
    rw [hStep, uc_qsum_snoc (m + n) g, uc_qsum_nat_add_split m n g,
        uc_qsum_snoc n (fun j => g (m + j))]
    omega

private theorem uc_qsum_mul_nat : ∀ (A B : Nat) (g : Nat → Nat),
    qsum (A * B) (fun i => g i.val) =
      qsum A (fun a => qsum B (fun b => g (a.val * B + b.val)))
  | 0, B, g => by
    rw [uc_qsum_nat_eq_of_eq (Nat.zero_mul B) g, qsum_zero, qsum_zero]
  | A + 1, B, g => by
    rw [uc_qsum_nat_eq_of_eq (Nat.succ_mul A B) g,
        uc_qsum_nat_add_split (A * B) B g,
        uc_qsum_mul_nat A B g,
        uc_qsum_snoc A (fun a => qsum B (fun b => g (a * B + b.val)))]

/-- Exact Fubini decomposition of `qsum (A * B)` over `ucPairFin`. -/
theorem qsum_ucPairFin {A B : Nat} (f : Fin (A * B) → Nat) :
    qsum (A * B) f = qsum A (fun a => qsum B (fun b => f (ucPairFin a b))) := by
  let g : Nat → Nat := fun n => if h : n < A * B then f ⟨n, h⟩ else 0
  have hL : qsum (A * B) f = qsum (A * B) (fun i => g i.val) :=
    qsum_congr (fun i => by
      dsimp only [g]
      split
      · rfl
      · next hn => exact absurd i.isLt hn)
  have hR : qsum A (fun a => qsum B (fun b => g (a.val * B + b.val))) =
      qsum A (fun a => qsum B (fun b => f (ucPairFin a b))) :=
    qsum_congr (fun a => qsum_congr (fun b => by
      dsimp only [g]
      split
      · rfl
      · next hn => exact absurd (ucPairFin a b).isLt hn))
  rw [hL, uc_qsum_mul_nat A B g, hR]

private theorem uc_qsum_mul_right : ∀ (n c : Nat) (f : Fin n → Nat),
    qsum n (fun i => f i * c) = qsum n f * c
  | 0, _, _ => by simp [qsum_zero]
  | n + 1, c, f => by
    simp only [qsum_succ, uc_qsum_mul_right n c, Nat.add_mul]

/-- Reducible session-product cardinality `ucPow C Q_s = C ^ Q_s`. -/
def ucPow (C : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => ucPow C k * C

theorem ucPow_zero (C : Nat) : ucPow C 0 = 1 := by rfl

theorem ucPow_succ (C k : Nat) : ucPow C (k + 1) = ucPow C k * C := by rfl

theorem ucPow_pos {C : Nat} (hC : 0 < C) : ∀ Q_s : Nat, 0 < ucPow C Q_s
  | 0 => by rw [ucPow_zero]; exact Nat.zero_lt_one
  | k + 1 => by rw [ucPow_succ]; exact Nat.mul_pos (ucPow_pos hC k) hC

theorem ucPow_eq_pow (C : Nat) : ∀ Q_s : Nat, ucPow C Q_s = C ^ Q_s
  | 0 => by rfl
  | k + 1 => by
    rw [ucPow_succ, ucPow_eq_pow C k, Nat.pow_succ]

/-- Update a single session slot `idx` in a `Q_s`-session tape vector `Fin Q_s → α`. -/
def updateFinVec {Q_s : Nat} {α : Type} (v : Fin Q_s → α) (idx : Fin Q_s) (x : α) :
    Fin Q_s → α :=
  fun j => if j = idx then x else v j

theorem updateFinVec_self {Q_s : Nat} {α : Type} (v : Fin Q_s → α) (idx : Fin Q_s) :
    updateFinVec v idx (v idx) = v := by
  funext j
  unfold updateFinVec
  by_cases hj : j = idx
  · rw [ite_eq_left hj, hj]
  · rw [ite_eq_right hj]

theorem updateFinVec_same {Q_s : Nat} {α : Type} (v : Fin Q_s → α) (idx : Fin Q_s) (x : α) :
    updateFinVec v idx x idx = x := by
  unfold updateFinVec
  exact ite_eq_left rfl

theorem updateFinVec_other {Q_s : Nat} {α : Type} (v : Fin Q_s → α) (idx j : Fin Q_s) (x : α)
    (hNe : j ≠ idx) :
    updateFinVec v idx x j = v j := by
  unfold updateFinVec
  exact ite_eq_right hNe

theorem updateFinVec_twice {Q_s : Nat} {α : Type} (v : Fin Q_s → α) (idx : Fin Q_s) (x y : α) :
    updateFinVec (updateFinVec v idx x) idx y = updateFinVec v idx y := by
  funext j
  unfold updateFinVec
  by_cases hj : j = idx
  · rw [ite_eq_left hj, ite_eq_left hj]
  · rw [ite_eq_right hj, ite_eq_right hj, ite_eq_right hj]

/-- Append one session coordinate onto `Fin k → α`. -/
def snocFinVec {k : Nat} {α : Type} (v : Fin k → α) (last : α) : Fin (k + 1) → α :=
  fun i => if h : i.val < k then v ⟨i.val, h⟩ else last

/-- Prefix projection of `Fin (k + 1) → α` onto `Fin k → α`. -/
def initFinVec {k : Nat} {α : Type} (v : Fin (k + 1) → α) : Fin k → α :=
  fun j => v ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩

private theorem initFinVec_snocFinVec {k : Nat} {α : Type} (v : Fin k → α) (last : α) :
    initFinVec (snocFinVec v last) = v := by
  funext j
  unfold initFinVec snocFinVec
  dsimp only
  split
  · rfl
  · next hn => exact absurd j.isLt hn

private theorem snocFinVec_last {k : Nat} {α : Type} (v : Fin k → α) (last : α) :
    snocFinVec v last ⟨k, Nat.lt_succ_self k⟩ = last := by
  unfold snocFinVec
  dsimp only
  split
  · next h => exact absurd h (Nat.lt_irrefl k)
  · rfl

private theorem snocFinVec_init_last {k : Nat} {α : Type} (w : Fin (k + 1) → α) :
    snocFinVec (initFinVec w) (w ⟨k, Nat.lt_succ_self k⟩) = w := by
  funext ⟨iv, isLt⟩
  unfold snocFinVec initFinVec
  dsimp only
  split
  · rfl
  · next hn =>
    have hEq : iv = k := by omega
    subst hEq
    rfl

/-- Constructive `0 Classical.choice` bijection `Fin (ucPow C Q_s) ≃ (Fin Q_s → Fin C)` (`0 < C`). -/
def finPowVecEquiv {C : Nat} (hC : 0 < C) :
    (Q_s : Nat) → SimpleEquiv (Fin (ucPow C Q_s)) (Fin Q_s → Fin C)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ⟨0, Nat.zero_lt_one⟩
      left_inv := fun ⟨v, hv⟩ => by
        have hv1 : v < 1 := hv
        have hv0 : v = 0 := by omega
        subst hv0
        rfl
      right_inv := fun f => funext (fun i => Fin.elim0 i) }
  | k + 1 =>
    let prev := finPowVecEquiv hC k
    { toFun := fun idx => snocFinVec (prev.toFun (ucSplitLeft hC idx)) (ucSplitRight hC idx)
      invFun := fun w => ucPairFin (prev.invFun (initFinVec w)) (w ⟨k, Nat.lt_succ_self k⟩)
      left_inv := fun idx => by
        change ucPairFin (prev.invFun (initFinVec (snocFinVec _ _)))
            (snocFinVec _ _ ⟨k, Nat.lt_succ_self k⟩) = idx
        rw [initFinVec_snocFinVec, prev.left_inv, snocFinVec_last]
        exact ucPair_split hC idx
      right_inv := fun w => by
        change snocFinVec (prev.toFun (ucSplitLeft hC (ucPairFin _ _)))
            (ucSplitRight hC (ucPairFin _ _)) = w
        rw [ucSplitLeft_pair hC, ucSplitRight_pair hC, prev.right_inv, snocFinVec_init_last] }

/-- Lift a coordinate bijection `bij v : SimpleEquiv (Fin C) (Fin C)` that does not depend on
    coordinate `idx` to a global bijection on `Fin Q_s → Fin C`. -/
def liftCoordVecEquiv {Q_s C : Nat} (idx : Fin Q_s)
    (bij : (Fin Q_s → Fin C) → SimpleEquiv (Fin C) (Fin C))
    (hIndep : ∀ (v : Fin Q_s → Fin C) (x y : Fin C),
      bij (updateFinVec v idx x) = bij (updateFinVec v idx y)) :
    SimpleEquiv (Fin Q_s → Fin C) (Fin Q_s → Fin C) :=
  have hInv : ∀ (v : Fin Q_s → Fin C) (x : Fin C), bij (updateFinVec v idx x) = bij v := by
    intro v x
    have h1 := hIndep v x (v idx)
    rw [updateFinVec_self] at h1
    exact h1
  { toFun := fun v => updateFinVec v idx ((bij v).toFun (v idx))
    invFun := fun w => updateFinVec w idx ((bij w).invFun (w idx))
    left_inv := fun v => by
      change updateFinVec (updateFinVec v idx ((bij v).toFun (v idx))) idx
        ((bij (updateFinVec v idx ((bij v).toFun (v idx)))).invFun
          (updateFinVec v idx ((bij v).toFun (v idx)) idx)) = v
      rw [hInv v ((bij v).toFun (v idx)), updateFinVec_same, (bij v).left_inv,
          updateFinVec_twice, updateFinVec_self]
    right_inv := fun w => by
      change updateFinVec (updateFinVec w idx ((bij w).invFun (w idx))) idx
        ((bij (updateFinVec w idx ((bij w).invFun (w idx)))).toFun
          (updateFinVec w idx ((bij w).invFun (w idx)) idx)) = w
      rw [hInv w ((bij w).invFun (w idx)), updateFinVec_same, (bij w).right_inv,
          updateFinVec_twice, updateFinVec_self] }

/-- Marginal Fubini slice bound over `ucPow C Q_s`: if fixing all coordinates `j ≠ idx` caps the
    slice sum over `x : Fin C` at `eps`, then the full product sum scaled by `C` is
    `≤ eps * ucPow C Q_s`. -/
theorem finPow_coord_sum_le {C : Nat} (hC : 0 < C) :
    ∀ (Q_s : Nat) (idx : Fin Q_s) (W : (Fin Q_s → Fin C) → Nat) (eps : Nat),
      (∀ v : Fin Q_s → Fin C, qsum C (fun x => W (updateFinVec v idx x)) ≤ eps) →
      qsum (ucPow C Q_s) (fun ω => W ((finPowVecEquiv hC Q_s).toFun ω)) * C ≤
        eps * ucPow C Q_s
  | 0, idx, _, _, _ => Fin.elim0 idx
  | k + 1, ⟨idxVal, idxIsLt⟩, W, eps, hSlice => by
    let idx : Fin (k + 1) := ⟨idxVal, idxIsLt⟩
    have hSplit :
        qsum (ucPow C (k + 1)) (fun ω => W ((finPowVecEquiv hC (k + 1)).toFun ω)) =
        qsum (ucPow C k) (fun pref =>
          qsum C (fun last => W (snocFinVec ((finPowVecEquiv hC k).toFun pref) last))) := by
      change qsum (ucPow C k * C) (fun ω => W ((finPowVecEquiv hC (k + 1)).toFun ω)) = _
      rw [qsum_ucPairFin]
      apply qsum_congr
      intro pref
      apply qsum_congr
      intro last
      change W (snocFinVec ((finPowVecEquiv hC k).toFun (ucSplitLeft hC (ucPairFin pref last)))
        (ucSplitRight hC (ucPairFin pref last))) = _
      rw [ucSplitLeft_pair hC, ucSplitRight_pair hC]
    rw [hSplit]
    by_cases hLt : idxVal < k
    · let idx' : Fin k := ⟨idxVal, hLt⟩
      rw [qsum_comm _ _ (fun (pref : Fin (ucPow C k)) (last : Fin C) =>
        W (snocFinVec ((finPowVecEquiv hC k).toFun pref) last))]
      rw [← uc_qsum_mul_right]
      have hEachLast : ∀ last : Fin C,
          qsum (ucPow C k) (fun pref =>
            W (snocFinVec ((finPowVecEquiv hC k).toFun pref) last)) * C ≤ eps * ucPow C k := by
        intro last
        apply finPow_coord_sum_le hC k idx' (fun u => W (snocFinVec u last)) eps
        intro u
        have hEqUpd : ∀ x : Fin C,
            snocFinVec (updateFinVec u idx' x) last = updateFinVec (snocFinVec u last) idx x := by
          intro x
          funext ⟨jv, jLt⟩
          unfold snocFinVec updateFinVec
          dsimp only
          split
          · next hj =>
            by_cases hEqJ : jv = idxVal
            · have h1 : (⟨jv, hj⟩ : Fin k) = idx' := Fin.ext hEqJ
              have h2 : (⟨jv, jLt⟩ : Fin (k + 1)) = idx := Fin.ext hEqJ
              rw [ite_eq_left h1, ite_eq_left h2]
            · have h1 : (⟨jv, hj⟩ : Fin k) ≠ idx' := fun he => hEqJ (congrArg Fin.val he)
              have h2 : (⟨jv, jLt⟩ : Fin (k + 1)) ≠ idx := fun he => hEqJ (congrArg Fin.val he)
              rw [ite_eq_right h1, ite_eq_right h2]
          · next hj =>
            have h2 : (⟨jv, jLt⟩ : Fin (k + 1)) ≠ idx := fun he => by
              have hv : jv = idxVal := congrArg Fin.val he
              exact hj (by omega)
            rw [ite_eq_right h2]
        have hCong : qsum C (fun x => W (snocFinVec (updateFinVec u idx' x) last)) =
            qsum C (fun x => W (updateFinVec (snocFinVec u last) idx x)) :=
          qsum_congr (fun x => congrArg W (hEqUpd x))
        rw [hCong]
        exact hSlice (snocFinVec u last)
      have hSumLe := qsum_le_qsum hEachLast
      rw [qsum_const] at hSumLe
      have hR : C * (eps * ucPow C k) = eps * ucPow C (k + 1) := by
        rw [ucPow_succ]
        ac_rfl
      rw [hR] at hSumLe
      exact hSumLe
    · have hIdxVal : idxVal = k := by omega
      have hEachPref : ∀ pref : Fin (ucPow C k),
          qsum C (fun last => W (snocFinVec ((finPowVecEquiv hC k).toFun pref) last)) ≤ eps := by
        intro pref
        let v0 := snocFinVec ((finPowVecEquiv hC k).toFun pref) ⟨0, hC⟩
        have hEqLast : ∀ last : Fin C,
            snocFinVec ((finPowVecEquiv hC k).toFun pref) last = updateFinVec v0 idx last := by
          intro last
          funext ⟨jv, jLt⟩
          unfold snocFinVec updateFinVec
          dsimp only
          split
          · next hj =>
            have hNe : (⟨jv, jLt⟩ : Fin (k + 1)) ≠ idx := fun he => by
              have hv : jv = idxVal := congrArg Fin.val he
              omega
            rw [ite_eq_right hNe]
            unfold v0 snocFinVec
            dsimp only
            split
            · rfl
            · next hn => exact absurd hj hn
          · next hj =>
            have hJvK : jv = idxVal := by omega
            have hEq : (⟨jv, jLt⟩ : Fin (k + 1)) = idx := Fin.ext hJvK
            rw [ite_eq_left hEq]
        rw [qsum_congr (fun last => congrArg W (hEqLast last))]
        exact hSlice v0
      have hPrefSum := qsum_le_qsum hEachPref
      rw [qsum_const] at hPrefSum
      have hMul := Nat.mul_le_mul_right C hPrefSum
      have hR : ucPow C k * eps * C = eps * ucPow C (k + 1) := by
        rw [ucPow_succ]
        ac_rfl
      rw [hR] at hMul
      exact hMul

/-- Single-coordinate concurrent hybrid hop over `ucPow C Q_s`. -/
theorem concurrent_coord_hop_bound {View : Type} {C Q_s : Nat} (hC : 0 < C)
    (idx : Fin Q_s)
    (G₀ G₁ : (Fin Q_s → Fin C) → View)
    (bij : (Fin Q_s → Fin C) → SimpleEquiv (Fin C) (Fin C))
    (hIndep : ∀ v x y, bij (updateFinVec v idx x) = bij (updateFinVec v idx y))
    (bad : (Fin Q_s → Fin C) → Bool) (eps : Nat)
    (hAgree : ∀ v, bad v = false → G₀ v = G₁ (updateFinVec v idx ((bij v).toFun (v idx))))
    (hBadSlice : ∀ v, qsum C (fun x => if bad (updateFinVec v idx x) then 1 else 0) ≤ eps)
    (D : View → Bool) :
    let enum := finPowVecEquiv hC Q_s
    natAbsDiff (qsum (ucPow C Q_s) (fun ω => if D (G₀ (enum.toFun ω)) then 1 else 0))
               (qsum (ucPow C Q_s) (fun ω => if D (G₁ (enum.toFun ω)) then 1 else 0)) * C ≤
      eps * ucPow C Q_s := by
  intro enum
  let eVec := liftCoordVecEquiv idx bij hIndep
  have hInv := qsum_bijection_invariant enum eVec (fun v => if D (G₁ v) then 1 else 0)
  have hDiff := qsum_indicator_diff_le
    (fun ω => D (G₀ (enum.toFun ω)))
    (fun ω => D (G₁ (eVec.toFun (enum.toFun ω))))
    (fun ω => bad (enum.toFun ω))
    (fun ω hb => congrArg D (hAgree (enum.toFun ω) hb))
  rw [hInv] at hDiff
  exact Nat.le_trans (Nat.mul_le_mul_right C hDiff)
    (finPow_coord_sum_le hC Q_s idx (fun v => if bad v then 1 else 0) eps hBadSlice)

/-- **Concurrent Product-Tape Hybrid Theorem (`concurrent_product_hybrid_bound`)**:
    Given `Q_s + 1` concurrent hybrids `hybrids h` (`0 ≤ h ≤ Q_s`) over `(Fin Q_s → Fin C)` (`0 < C`),
    if each per-session hop `idx → idx + 1` agrees along a context-compatible coordinate bijection
    outside a bad event of slice cardinality `≤ eps` out of `C`, then for EVERY distinguisher `D`,
    the total distinguishing count scaled by `C` is at most `(Q_s * eps) * ucPow C Q_s`. -/
theorem concurrent_product_hybrid_bound {View : Type} {C Q_s : Nat} (hC : 0 < C)
    (hybrids : (h : Nat) → h ≤ Q_s → (Fin Q_s → Fin C) → View)
    (bij : (idx : Fin Q_s) → (Fin Q_s → Fin C) → SimpleEquiv (Fin C) (Fin C))
    (hIndep : ∀ idx v x y, bij idx (updateFinVec v idx x) = bij idx (updateFinVec v idx y))
    (bad : Fin Q_s → (Fin Q_s → Fin C) → Bool)
    (eps : Nat)
    (hAgree : ∀ (idx : Fin Q_s) v, bad idx v = false →
      hybrids idx.val (Nat.le_of_lt idx.isLt) v =
        hybrids (idx.val + 1) idx.isLt (updateFinVec v idx ((bij idx v).toFun (v idx))))
    (hBadSlice : ∀ (idx : Fin Q_s) v,
      qsum C (fun x => if bad idx (updateFinVec v idx x) then 1 else 0) ≤ eps)
    (D : View → Bool) :
    let enum := finPowVecEquiv hC Q_s
    let acc := fun (h : Nat) (hh : h ≤ Q_s) =>
      qsum (ucPow C Q_s) (fun ω => if D (hybrids h hh (enum.toFun ω)) then 1 else 0)
    natAbsDiff (acc 0 (Nat.zero_le Q_s)) (acc Q_s (Nat.le_refl Q_s)) * C ≤
      (Q_s * eps) * ucPow C Q_s := by
  intro enum acc
  have hTel : ∀ (k : Nat) (hk : k ≤ Q_s),
      natAbsDiff (acc 0 (Nat.zero_le Q_s)) (acc k hk) * C ≤ (k * eps) * ucPow C Q_s := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [natAbsDiff_eq]
    | succ k ih =>
      intro hkSucc
      have hkLe : k ≤ Q_s := Nat.le_of_lt hkSucc
      have ihK := ih hkLe
      let idx : Fin Q_s := ⟨k, hkSucc⟩
      have hStep := concurrent_coord_hop_bound hC idx
        (hybrids k hkLe) (hybrids (k + 1) hkSucc)
        (bij idx) (hIndep idx) (bad idx) eps (hAgree idx) (hBadSlice idx) D
      have hTri := Nat.mul_le_mul_right C
        (natAbsDiff_triangle (acc 0 (Nat.zero_le Q_s)) (acc k hkLe) (acc (k + 1) hkSucc))
      rw [Nat.add_mul] at hTri
      have hSum := Nat.add_le_add ihK hStep
      have hR : (k * eps) * ucPow C Q_s + eps * ucPow C Q_s = ((k + 1) * eps) * ucPow C Q_s := by
        rw [Nat.succ_mul, Nat.add_mul]
      rw [hR] at hSum
      exact Nat.le_trans hTri hSum
  exact hTel Q_s (Nat.le_refl Q_s)

end Qsag
end

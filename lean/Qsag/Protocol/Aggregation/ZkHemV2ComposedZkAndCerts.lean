module
public import Qsag.Protocol.Aggregation.ZkHemV2ScheduleCert
public import Qsag.Protocol.Aggregation.ZkHemV2
public import Qsag.Protocol.Aggregation.ZkHem
public import Qsag.Protocol.Aggregation.ClosedWhirSchedule
public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Math.PolyRing
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
import Qsag.Math.Tactic.MaskBijection
import Qsag.Math.Tactic.CommRing

/-!
# Zk-Hem v2 joint views and production schedule obligations

The LogUp disclosure includes both public refusal conditions. The Stage-0
simulator couples the coefficient tape to the sequence of actual projected
polynomial folds. Revealing the complete remainders as well admits a
coefficient-recovery counterexample. The last section connects decoded GS
lists and authenticated tables to the deployed schedule family, and identifies
the Stage-0 counting obligation for a single 400-bit challenge.
-/

public section
namespace Qsag.ZkHemV2
open CommRingOps
set_option autoImplicit false
set_option maxRecDepth 12000

local notation "E" => QuinticGoldilocks

/-- Equality-polynomial weights on the eight corners, low bit first. -/
def lookupCornerWeight (r₀ r₁ r₂ : E) (i : Nat) : E :=
  let bit (r : E) (j : Nat) := if i.testBit j then r else sub one r
  mul (mul (bit r₀ 0) (bit r₁ 1)) (bit r₂ 2)

private def limb (x : E) : Nat → Goldilocks
  | 0 => x.c0 | 1 => x.c1 | 2 => x.c2 | 3 => x.c3 | _ => x.c4

private def fromLimbs (x : Nat → Goldilocks) : E := ⟨x 0,x 1,x 2,x 3,x 4⟩

private theorem limb_fromLimbs (x : Nat → Goldilocks) {j : Nat} (hj : j < 5) :
    limb (fromLimbs x) j = x j := by
  rcases j with _|_|_|_|_|j <;> first | rfl | omega

/-- The five independent base cells are stored in a five-component record.
    Each multiplies its own extension-field corner weight. -/
def lookupPadSum (u : Nat → E) (pads : E) : E :=
  Mat.rangeSum 5 (fun i => mul (u i) (QuinticGoldilocks.ofBase (limb pads i)))

/-- Rows are indexed by pads and columns by power-basis coefficients. -/
def lookupPadDet (u : Nat → E) : Goldilocks := Mat.det 5 (fun i => limb (u i))

private theorem limb_add (x y : E) (j : Nat) :
    limb (add x y) j = add (limb x j) (limb y j) := by
  rcases j with _|_|_|_|j <;> rfl

private theorem limb_zero (j : Nat) : limb (zero : E) j = zero := by
  rcases j with _|_|_|_|j <;> rfl

private theorem limb_scale (x : E) (a : Goldilocks) (j : Nat) :
    limb (mul x (QuinticGoldilocks.ofBase a)) j = mul a (limb x j) := by
  rw [QuinticGoldilocks.mul_ofBase, LawfulCommRing.mul_comm a]
  rcases j with _|_|_|_|j <;> rfl

private theorem limb_sum (f : Nat → E) (n j : Nat) :
    limb (Mat.rangeSum n f) j = Mat.rangeSum n (fun i => limb (f i) j) := by
  induction n with
  | zero => simpa only [Mat.rangeSum_zero] using limb_zero j
  | succ n ih => simp only [Mat.rangeSum.public_eqs, limb_add, ih]

private theorem recoverCoordinate (u : Nat → E) (pads : E) {i : Nat} (hi : i < 5) :
    Mat.det 5 (Mat.updRow (fun j => limb (u j)) i (limb (lookupPadSum u pads))) =
      mul (limb pads i) (lookupPadDet u) := by
  let m := fun j => limb (u j)
  have hrow : limb (lookupPadSum u pads) =
      fun j => Mat.rangeSum 5 (fun t => mul (limb pads t) (m t j)) := by
    funext j
    simp only [lookupPadSum, limb_sum, limb_scale, m]
  rw [hrow, Mat.det_updRow_rangeSum 5 i m hi, Mat.rangeSum_single hi]
  · apply congrArg (mul (limb pads i))
    apply Mat.det_congr
    intro a _ b _
    by_cases ha : a = i <;> simp [Mat.updRow.public_eqs, ha, m]
  · intro j hj hji
    suffices h : Mat.det 5 (Mat.updRow m i (m j)) = zero by rw [h, LawfulCommRing.mul_zero]
    by_cases h : j < i
    · apply Mat.det_eq_zero_of_row_eq 5 j i _ h hi
      intro a _
      simp [Mat.updRow.public_eqs, hji]
    · apply Mat.det_eq_zero_of_row_eq 5 i j _ (by omega) hj
      intro a _
      simp [Mat.updRow.public_eqs, hji]

/-- Cramer's rule gives the actual base-cell inverse. -/
private def recoverPads (u : Nat → E) (v : E) : E :=
  fromLimbs fun i => mul (Mat.det 5 (Mat.updRow (fun j => limb (u j)) i (limb v)))
    (LawfulField.inv (lookupPadDet u))

private theorem recoverPads_left (u : Nat → E) (hu : lookupPadDet u ≠ zero) (x : E) :
    recoverPads u (lookupPadSum u x) = x := by
  have h {i : Nat} (hi : i < 5) :
      limb (recoverPads u (lookupPadSum u x)) i = limb x i := by
    unfold recoverPads
    rw [limb_fromLimbs _ hi, recoverCoordinate u x hi, LawfulCommRing.mul_assoc,
      LawfulField.mul_inv_cancel hu, LawfulCommRing.mul_one]
  exact QuinticGoldilocks.ext (h (i := 0) (by decide)) (h (i := 1) (by decide))
    (h (i := 2) (by decide)) (h (i := 3) (by decide)) (h (i := 4) (by decide))

private def baseElements := List.ofFn (n := goldilocksPrime) (fun i => (⟨i.val,i.isLt⟩ : Goldilocks))
private theorem baseMember (x : Goldilocks) : x ∈ baseElements :=
  List.mem_ofFn.mpr ⟨⟨x.val,x.isLt⟩,rfl⟩

private def quinticElements : List E :=
  baseElements.flatMap fun a => baseElements.flatMap fun b => baseElements.flatMap fun c =>
    baseElements.flatMap fun d => baseElements.map fun e => ⟨a,b,c,d,e⟩

private theorem quinticMember (x : E) : x ∈ quinticElements := by
  simp only [quinticElements, List.mem_flatMap, List.mem_map]
  exact ⟨x.c0,baseMember _,x.c1,baseMember _,x.c2,baseMember _,x.c3,baseMember _,
    x.c4,baseMember _,rfl⟩

private theorem finite_right_inverse {T : Type} [DecidableEq T] (pool : List T)
    (hall : ∀ x, x ∈ pool) (f g : T → T) (h : ∀ x, g (f x) = x) (y : T) : f (g y) = y := by
  let xs := JohnsonBound.dedupFirst pool
  have hc (x : T) : x ∈ xs := (JohnsonBound.mem_dedupFirst_iff x _).mpr (hall x)
  have hn : xs.Nodup := JohnsonBound.dedupFirst_nodup _
  have hm : (xs.map f).Nodup := hn.map f (fun a b hab he =>
    hab ((h a).symm.trans ((congrArg g he).trans (h b))))
  if hy : y ∈ xs.map f then
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    rw [h]
  else
    have hle := nodup_length_le_of_subset (List.nodup_cons.mpr ⟨hy,hm⟩)
      (M := xs) (fun x _ => hc x)
    simp only [List.length_cons, List.length_map] at hle
    omega

def lookupPadEquiv (u : Nat → E) (h : lookupPadDet u ≠ zero) : SimpleEquiv E E where
  toFun := lookupPadSum u
  invFun := recoverPads u
  left_inv := recoverPads_left u h
  right_inv := finite_right_inverse quinticElements quinticMember _ _ (recoverPads_left u h)

#print axioms lookupPadEquiv

abbrev LookupTriple := QuinticGoldilocks × QuinticGoldilocks × QuinticGoldilocks

/-- Two groups of five independent base cells and one free helper extension
    cell. The checked rows and the seven other helper cells enter the offsets. -/
def logUpFullRankJointMaskView (u : Nat → E) (k : E) (d coins : LookupTriple) : LookupTriple :=
  (add d.1 (mul k (lookupPadSum u coins.1)),
   add d.2.1 (mul k (lookupPadSum u coins.2.1)),
   add d.2.2 (mul (mul k (u 0)) coins.2.2))

private def affineCoord (k d : E) (hk : k ≠ zero) (b : SimpleEquiv E E) : SimpleEquiv E E where
  toFun x := add d (mul k (b.toFun x))
  invFun y := b.invFun (mul (sub y d) (LawfulField.inv k))
  left_inv x := by
    have he := congrFun (unmaskLine_maskLine k hk (fun _ : Unit => d) (fun _ => b.toFun x)) ()
    simpa only [unmaskLine.public_eqs, maskLine] using (congrArg b.invFun he).trans (b.left_inv x)
  right_inv y := by
    rw [b.right_inv]
    simpa only [unmaskLine.public_eqs, maskLine] using congrFun (maskLine_unmaskLine k hk (fun _ : Unit => d) (fun _ => y)) ()

private def equivProd {A B C D : Type} (e : SimpleEquiv A C) (f : SimpleEquiv B D) :
    SimpleEquiv (A × B) (C × D) where
  toFun x := (e.toFun x.1, f.toFun x.2)
  invFun y := (e.invFun y.1, f.invFun y.2)
  left_inv x := Prod.ext (e.left_inv x.1) (f.left_inv x.2)
  right_inv y := Prod.ext (e.right_inv y.1) (f.right_inv y.2)

/-- The nonzero diagonal determinant is the public Rust rank check after
    converting the two five-cell blocks to extension-field coordinates. -/
theorem logUp_joint_rank15 (u : Nat → E) (k : E) (hu : lookupPadDet u ≠ zero)
    (hdiag : mul (mul k k) (mul k (u 0)) ≠ zero) :
    CoinBijectionSimulated (logUpFullRankJointMaskView u k) id := by
  have hk : k ≠ zero := by
    intro h; apply hdiag; rw [h, LawfulCommRing.zero_mul, LawfulCommRing.zero_mul]
  have hlast : mul k (u 0) ≠ zero := by
    intro h; apply hdiag; rw [h, LawfulCommRing.mul_zero]
  intro d
  exact ⟨equivProd (affineCoord k d.1 hk (lookupPadEquiv u hu))
    (equivProd (affineCoord k d.2.1 hk (lookupPadEquiv u hu))
      (affineCoord _ d.2.2 hlast (SimpleEquiv.refl _))), fun _ => rfl⟩

/-- All public table rows occur in the checked prefix, including zero-weight
    rows. Satisfying query rows add no new compressed value. -/
def lookupPoles (table : List E) (padding : Bool) : List E :=
  if padding then zero :: table else table

theorem lookup_retry_iff_public (table query : List E) (padding : Bool)
    (satisfying : ∀ v ∈ query, v ∈ table) (α : E) :
    (∃ v ∈ query ++ lookupPoles table padding, sub α v = zero) ↔
      α ∈ lookupPoles table padding := by
  constructor
  · rintro ⟨v,hv,h⟩
    have e := LawfulCommRing.sub_eq_zero_iff.mp h
    subst α
    rcases List.mem_append.mp hv with hq | hp
    · cases padding <;> first | exact satisfying _ hq | exact List.mem_cons_of_mem _ (satisfying _ hq)
    · exact hp
  · intro h
    exact ⟨α, List.mem_append_right _ h, LawfulCommRing.sub_self _⟩

/-- The product of the actual denominators is tested before any inversion. -/
def denominatorProduct (α : E) : List E → E
  | [] => one
  | v :: vs => mul (sub α v) (denominatorProduct α vs)

private theorem prod_zero_iff (α : E) (vs : List E) :
    denominatorProduct α vs = zero ↔ ∃ v ∈ vs, sub α v = zero := by
  induction vs with
  | nil =>
    constructor
    · intro h; exact False.elim (LawfulField.one_ne_zero h)
    · rintro ⟨v,h,_⟩; cases h
  | cons a as ih =>
    change mul _ _ = _ ↔ _
    by_cases ha : sub α a = zero
    · constructor
      · intro _; exact ⟨a,List.mem_cons_self,ha⟩
      · intro _; rw [ha, LawfulCommRing.zero_mul]
    · constructor
      · intro h
        have hv : denominatorProduct α as = zero := by
          have t := congrArg (mul (LawfulField.inv (sub α a))) h
          rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (LawfulField.inv _),
            LawfulField.mul_inv_cancel ha, LawfulCommRing.one_mul, LawfulCommRing.mul_zero] at t
          exact t
        obtain ⟨v,hv,he⟩ := ih.mp hv
        exact ⟨v,List.mem_cons_of_mem _ hv,he⟩
      · rintro ⟨v,hv,he⟩
        rcases List.mem_cons.mp hv with rfl | h
        · exact False.elim (ha he)
        · rw [ih.mpr ⟨v,h,he⟩, LawfulCommRing.mul_zero]

theorem lookup_product_retry_public (table query : List E) (padding : Bool)
    (sat : ∀ v ∈ query, v ∈ table) (α : E) :
    denominatorProduct α (query ++ lookupPoles table padding) = zero ↔
      α ∈ lookupPoles table padding :=
  (prod_zero_iff _ _).trans (lookup_retry_iff_public table query padding sat α)

#print axioms logUp_joint_rank15
#print axioms lookup_product_retry_public

/-- The Rust rank matrix has a row per limb and a column per corner. -/
def lookupLimbDet (u : Nat → E) : Goldilocks :=
  Mat.det 5 (fun i j => limb (u j) i)

set_option maxHeartbeats 1400000 in
private theorem det5_transpose {F : Type} [LawfulCommRing F] (m : Nat → Nat → F) :
    Mat.det 5 (fun i j => m j i) = Mat.det 5 m := by
  simp (config := { maxSteps := 1000000 }) only [Mat.det.public_eqs, Mat.rangeSum.public_eqs, Mat.signed.public_eqs, Mat.minor.public_eqs,
    Mat.skipIdx.public_eqs, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceLT, ite_true, ite_false,
    LawfulCommRing.zero_add, LawfulCommRing.mul_one]
  constructive_ring

theorem lookupLimbDet_eq (u : Nat → E) : lookupLimbDet u = lookupPadDet u :=
  det5_transpose (fun j => limb (u j))

inductive LookupDisclosure where
  | poleRetry
  | rankRetry
  | values (out : LookupTriple)

def lookupRankGood (u : Nat → E) (k : E) : Bool :=
  decide (lookupLimbDet u ≠ zero ∧ mul (mul k k) (mul k (u 0)) ≠ zero)

/-- Simulation of the joint lookup disclosure including both public refusal
    paths. The first test uses every checked denominator, before inversion.
    The two independent base-pad arrays each use five coordinates. -/
theorem lookup_disclosure_with_retries {W : Type}
    (r₀ r₁ r₂ : E) (upper : List E) (table : List E) (padding : Bool) (α : E)
    (query : W → List E) (sat : ∀ w v, v ∈ query w → v ∈ table) (offset : W → LookupTriple) :
    let u := lookupCornerWeight r₀ r₁ r₂
    let k := upper.foldl mul one
    CoinBijectionSimulated
      (fun (w : W) (r : LookupTriple) =>
        if denominatorProduct α (query w ++ lookupPoles table padding) = zero then LookupDisclosure.poleRetry
        else if lookupRankGood u k then .values (logUpFullRankJointMaskView u k (offset w) r) else .rankRetry)
      (fun (v : LookupTriple) => if α ∈ lookupPoles table padding then LookupDisclosure.poleRetry
        else if lookupRankGood u k then .values v else .rankRetry) := by
  intro u k w
  have he := lookup_product_retry_public table (query w) padding (sat w) α
  by_cases hp : α ∈ lookupPoles table padding
  · exact ⟨SimpleEquiv.refl _, fun _ => by simp only [hp, he.mpr hp, ite_true]⟩
  · have hn := mt he.mp hp
    cases hg : lookupRankGood u k with
    | false => exact ⟨SimpleEquiv.refl _, fun _ => by simp only [hp,hn,ite_false,Bool.false_eq_true]⟩
    | true =>
      have h := of_decide_eq_true (show decide _ = true from hg)
      obtain ⟨e,eq⟩ := logUp_joint_rank15 u k ((lookupLimbDet_eq u) ▸ h.1) h.2 (offset w)
      exact ⟨e, fun r => by simp only [hp,hn,ite_false,ite_true]; exact congrArg LookupDisclosure.values (eq r)⟩

/-- Concrete good verifier coins from the V2.1 basis witness. -/
theorem lookup_rank_witness :
    let x := QuinticGoldilocks.xBasis
    let x₂ := mul x x
    let u := lookupCornerWeight x x₂ (mul x₂ x₂)
    lookupLimbDet u = Goldilocks.ofNat 16 ∧ lookupRankGood u one = true := by
  intro x x₂ u
  have hd : lookupLimbDet u = Goldilocks.ofNat 16 := by
    simp only [lookupLimbDet, Mat.det.public_eqs, Mat.rangeSum.public_eqs, Mat.minor.public_eqs,
      Mat.skipIdx.public_eqs, Mat.signed.public_eqs, Nat.reduceAdd, Nat.reduceMod,
      Nat.reduceEqDiff, Nat.reduceLT, ite_true, ite_false]
    decide +revert +kernel
  refine ⟨hd, ?_⟩
  rw [lookupRankGood, hd]
  clear hd
  decide +revert +kernel

#print axioms lookup_disclosure_with_retries
#print axioms lookup_rank_witness

/-! ## Joint simulation and observability of complete residues -/

abbrev FiveFoldCells := {v : List QuinticGoldilocks // v.length = 5}
abbrev ResidueCoordinates (s : Nat) (qs : List Goldilocks) (ωs : List E) :=
  {us : List Goldilocks // us.length = qs.length} ×
  {rs : List (List E) // rs.length = ωs.length ∧ ∀ r ∈ rs, r.length = 2^s}
abbrev BlinderCoefficients (s : Nat) (qs : List Goldilocks) (ωs : List E) :=
  {cs : List Goldilocks // cs.length = qs.length + 5 * (ωs.length * 2^s)}

def maskedResidues (s shiftDeg : Nat) (qs : List Goldilocks) (ωs : List E)
    (d : ResidueCoordinates s qs ωs) (c : BlinderCoefficients s qs ωs) :=
  let b := blindingResidueView s shiftDeg qs ωs c.val
  (ZkHem.vadd d.1.val b.1, vaddResidues d.2.val b.2)

/-- Composition for the four component interfaces on separately supplied tapes.
    The word and all offsets may come from the same witness. Condition on the
    seven remaining helper pads by including their contribution in the lookup offset. -/
theorem four_view_product_tapes {ι κ W : Type} (β φ : E) (hβ : β ≠ zero) (hφ : φ ≠ zero)
    (ℓ : ZkHem.LinForm ι E) (opened : κ → ZkHem.LinForm ι E) (σ : E) (o : κ → E)
    (word : W → {P : ι → E // ℓ.app P = σ ∧ ∀ i, (opened i).app P = o i})
    (xs ws : List E) (hnd : xs.Nodup) (hx : ∀ x ∈ xs, x ≠ zero) (hw : ∀ w ∈ ws, w ≠ zero)
    (hlx : xs.length = 5) (hlw : ws.length = 5) (fd : W → FiveFoldCells)
    (s shiftDeg : Nat) (qs : List Goldilocks) (ωs : List E)
    (hqs : qs.Nodup) (hqz : ∀ q ∈ qs, q ≠ zero) (hv : MaskRootsValid s ωs)
    (rd : W → ResidueCoordinates s qs ωs) (k : E) (u : Nat → E)
    (hu : lookupPadDet u ≠ zero) (hk : mul (mul k k) (mul k (u 0)) ≠ zero)
    (ld : W → LookupTriple) (table : List E) (padding : Bool) (α : E) (query : W → List E)
    (sat : ∀ w v, v ∈ query w → v ∈ table) :
    CoinBijectionSimulated
      (fun (w : W) (c : (ι → E) × FiveFoldCells × BlinderCoefficients s qs ωs × LookupTriple) =>
        if denominatorProduct α (query w ++ lookupPoles table padding) = zero then none else
          some (maskLineReal β ℓ opened (word w).val c.1,
            ZkHem.vadd (fd w).val (foldScalars φ xs ws c.2.1.val),
            maskedResidues s shiftDeg qs ωs (rd w) c.2.2.1,
            logUpFullRankJointMaskView u k (ld w) c.2.2.2))
      (fun (t : (ι → E) × FiveFoldCells × ResidueCoordinates s qs ωs × LookupTriple) =>
        if α ∈ lookupPoles table padding then none else
          some (maskLineSim β ℓ opened σ o t.1, t.2.1.val,
            (t.2.2.1.1.val, t.2.2.1.2.val), t.2.2.2)) := by
  intro w
  obtain ⟨m,hm⟩ := v2_mask_line_view_perfectly_simulated β hβ ℓ opened σ o (word w)
  obtain ⟨f,hf⟩ := v2_fold_scalars_perfectly_simulated φ xs ws hnd hx hw hφ hlx hlw (fd w)
  obtain ⟨b,hb⟩ := v2_blinding_residue_ring_perfectly_simulated s shiftDeg qs ωs hqs hqz hv (rd w)
  obtain ⟨l,hl⟩ := logUp_joint_rank15 u k hu hk (ld w)
  refine ⟨equivProd m (equivProd f (equivProd b l)), fun c => ?_⟩
  have hp := lookup_product_retry_public table (query w) padding (sat w) α
  by_cases h : α ∈ lookupPoles table padding
  · simp only [h, hp.mpr h, ite_true]
  · have hn := mt hp.mp h
    simp only [hn, h, ite_false]
    apply congrArg some
    exact Prod.ext (hm c.1) (Prod.ext (hf c.2.1) (Prod.ext (hb c.2.2.1) (hl c.2.2.2)))

/-- In the shared-blinder experiment a fold contribution is observable once
    its full source residues are disclosed. A witness-dependent residual
    offset can then be recovered exactly from the second fold scalar. -/
def evenPartAt (x : E) : List E → E
  | [] => zero
  | [a] => a
  | a :: _ :: cs => add a (mul (mul x x) (evenPartAt x cs))

private theorem evenPart_double (x : E) : ∀ cs : List E,
    mul (evenPartAt x cs) (add one one) =
      add (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs cs (neg x))
  | [] => by change mul zero (add one one) = add zero (zero : E); constructive_ring
  | [a] => by simp only [evenPartAt, RoundPoly.evalCoeffs]; constructive_ring
  | a :: b :: cs => by
    have h := evenPart_double x cs
    simp only [evenPartAt, RoundPoly.evalCoeffs_cons]
    calc
      _ = add (mul a (add one one)) (mul (mul x x) (mul (evenPartAt x cs) (add one one))) := by constructive_ring
      _ = _ := by rw [h]; constructive_ring

private theorem neg_even_pow (x : E) : ∀ n, fpow (neg x) (2*n) = fpow x (2*n)
  | 0 => by simp only [Nat.mul_zero, fpow.public_eqs]
  | n+1 => by
    rw [show 2*(n+1) = 2*n+1+1 by omega]
    simp only [fpow.public_eqs, neg_even_pow x n]
    constructive_ring

/-- The actual even-part evaluation in the first fold is completely
    determined by the remainder at its mask point. Both x and -x are roots. -/
theorem evenPartAt_residue (s : Nat) (x : E) (p : List E) :
    evenPartAt x (divModBinomial (2^(s+1)-1) (fpow x (2^(s+1))) p).1 = evenPartAt x p := by
  let n := 2^(s+1)
  have hn : n-1+1 = n := by have : 0 < n := Nat.two_pow_pos _; omega
  have hp : fpow x (n-1+1) = fpow x n := by rw [hn]
  have hm : fpow (neg x) (n-1+1) = fpow x n := by
    rw [hn, show n = 2*(2^s) by dsimp [n]; rw [Nat.pow_succ, Nat.mul_comm]]
    exact neg_even_pow _ _
  let rem := (divModBinomial (n-1) (fpow x n) p).1
  have h : mul (evenPartAt x rem) (add one one) = mul (evenPartAt x p) (add one one) := by
    rw [evenPart_double, evenPart_double, evalCoeffs_divModBinomial_at_root _ _ _ hp,
      evalCoeffs_divModBinomial_at_root _ _ _ hm]
  have hnz : (add one one : E) ≠ zero := by decide +kernel
  have h' := congrArg (fun v => mul v (LawfulField.inv (add one one : E))) h
  rwa [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hnz,
    LawfulCommRing.mul_one, LawfulCommRing.mul_one] at h'

def foldTauFromResidues (xs ws : List E) (rs : List (List E)) : E :=
  rowSum id xs ws (List.zipWith evenPartAt xs rs)

#print axioms four_view_product_tapes

/-- Quotient remainders of the whole masked polynomial, in point order. -/
noncomputable def maskPointResidues (s : Nat) (xs : List E) (p : List E) : List (List E) :=
  xs.map fun x => (divModBinomial (2^(s+1)-1) (fpow x (2^(s+1))) p).1

private theorem pointTermsFromResidues (s : Nat) (p : List E) (xs : List E) :
    List.zipWith evenPartAt xs (maskPointResidues s xs p) = xs.map (fun x => evenPartAt x p) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change evenPartAt a _ :: List.zipWith evenPartAt xs (maskPointResidues s xs p) = _ :: _
    rw [evenPartAt_residue, ih]

/-- Specialize the first WHIR fold to the public coefficient kernel e₁.
    Its claim is coefficient one. The non-point part of τ₀₁ is coefficient zero
    because the odd half of e₁ has its sole one at position zero. -/
def tau01AtLinearCoefficientClaim (xs ws : List E) (p : List E) : E :=
  add (p.headD zero) (rowSum id xs ws (xs.map fun x => evenPartAt x p))

theorem full_residue_tau01_recovers_constant (s : Nat) (xs ws p : List E) :
    sub (tau01AtLinearCoefficientClaim xs ws p) (foldTauFromResidues xs ws (maskPointResidues s xs p)) =
      p.headD zero := by
  simp only [tau01AtLinearCoefficientClaim, foldTauFromResidues, pointTermsFromResidues]
  constructive_ring

/-- Two base-field words with the same public coefficient-one claim. Any
    blinding polynomial placed at degree two or higher leaves that claim zero.
    Coupling the full quotient residues and τ₀₁ forces the two secrets equal. -/
theorem shared_polynomial_views_obstruct_full_sim {C : Type} (s gap blindCount : Nat) (xs ws : List E)
    (sim : C → List (List E) × E) :
    ¬ CoinBijectionSimulated
      (fun (secret : Goldilocks) (blind : Fin blindCount → Goldilocks) =>
        let p := QuinticGoldilocks.ofBase secret :: zero ::
          (List.replicate gap zero ++ List.ofFn (fun i => QuinticGoldilocks.ofBase (blind i)))
        (maskPointResidues s xs p, tau01AtLinearCoefficientClaim xs ws p)) sim := by
  intro h
  obtain ⟨e₀,h₀⟩ := h zero
  obtain ⟨e₁,h₁⟩ := h one
  let b₀ : Fin blindCount → Goldilocks := fun _ => zero
  let b₁ := e₁.invFun (e₀.toFun b₀)
  have he : e₁.toFun b₁ = e₀.toFun b₀ := e₁.right_inv _
  have eqv := (h₀ b₀).trans ((congrArg sim he).symm.trans (h₁ b₁).symm)
  have decoded := congrArg (fun v : List (List E) × E => sub v.2 (foldTauFromResidues xs ws v.1)) eqv
  dsimp only at decoded
  rw [full_residue_tau01_recovers_constant, full_residue_tau01_recovers_constant] at decoded
  exact LawfulField.one_ne_zero (QuinticGoldilocks.ofBase_injective decoded).symm

#print axioms evenPartAt_residue
#print axioms shared_polynomial_views_obstruct_full_sim

abbrev ResidueLookupView := (List Goldilocks × List (List QuinticGoldilocks)) × LookupTriple

def residueLookupPrefix {W : Type} (s shiftDeg : Nat) (qs : List Goldilocks) (xs : List E)
    (rd : W → ResidueCoordinates s qs xs) (u : Nat → E) (k : E) (ld : W → LookupTriple)
    (w : W) (coins : BlinderCoefficients s qs xs × LookupTriple) : ResidueLookupView :=
  (maskedResidues s shiftDeg qs xs (rd w) coins.1, logUpFullRankJointMaskView u k (ld w) coins.2)

def simulatedPrefix {s : Nat} {qs : List Goldilocks} {xs : List E}
    (t : ResidueCoordinates s qs xs × LookupTriple) : ResidueLookupView :=
  ((t.1.1.val,t.1.2.val),t.2)

private def equivOver {A B C D : Type} (e : SimpleEquiv A B) (f : A → SimpleEquiv C D) :
    SimpleEquiv (A × C) (B × D) where
  toFun p := (e.toFun p.1, (f p.1).toFun p.2)
  invFun q := (e.invFun q.1, (f (e.invFun q.1)).invFun q.2)
  left_inv p := by simp only [e.left_inv, (f _).left_inv]
  right_inv q := by simp only [e.right_inv, (f _).right_inv]

noncomputable def sharedFoldView (φ : E) (xs ws : List E) (offset : FiveFoldCells) (pr : ResidueLookupView) :=
  ZkHem.vadd offset.val (foldScalars φ xs ws (List.zipWith evenPartAt xs pr.1.2))

/-- A single coupled experiment on the actual shared residue tape. The word
    entering the mask line may depend on every preceding real coin. Publishing
    the complete residues requires the residual fold offset, the mask claim
    and its opened projections to be public functions of the disclosed prefix. -/
theorem shared_tape_four_view_simulation {ι κ W : Type}
    (s shiftDeg : Nat) (qs : List Goldilocks) (xs ws : List E) (φ β : E) (hβ : β ≠ zero)
    (hqs : qs.Nodup) (hqz : ∀ q ∈ qs, q ≠ zero) (hv : MaskRootsValid s xs)
    (rd : W → ResidueCoordinates s qs xs) (u : Nat → E) (k : E) (ld : W → LookupTriple)
    (hu : lookupLimbDet u ≠ zero) (hk : mul (mul k k) (mul k (u 0)) ≠ zero)
    (ℓ : ZkHem.LinForm ι E) (openings : κ → ZkHem.LinForm ι E)
    (word : W → BlinderCoefficients s qs xs × LookupTriple → ι → E)
    (foldOffset : W → BlinderCoefficients s qs xs × LookupTriple → FiveFoldCells)
    (σ : ResidueLookupView → E) (o : ResidueLookupView → κ → E)
    (publicOffset : ResidueLookupView → FiveFoldCells)
    (table : List E) (padding : Bool) (α : E) (query : W → List E)
    (satisfying : ∀ w v, v ∈ query w → v ∈ table) :
    let pre := residueLookupPrefix s shiftDeg qs xs rd u k ld
    (∀ w a, ℓ.app (word w a) = σ (pre w a) ∧
      (∀ j, (openings j).app (word w a) = o (pre w a) j) ∧ foldOffset w a = publicOffset (pre w a)) →
    CoinBijectionSimulated
      (fun (w : W) (c : (BlinderCoefficients s qs xs × LookupTriple) × (ι → E)) =>
        let v := pre w c.1
        if denominatorProduct α (query w ++ lookupPoles table padding) = zero then none else
          some (maskLineReal β ℓ openings (word w c.1) c.2,
            sharedFoldView φ xs ws (foldOffset w c.1) v, v.1, v.2))
      (fun (t : (ResidueCoordinates s qs xs × LookupTriple) × (ι → E)) =>
        let v := simulatedPrefix t.1
        if α ∈ lookupPoles table padding then none else
          some (maskLineSim β ℓ openings (σ v) (o v) t.2,
            sharedFoldView φ xs ws (publicOffset v) v, v.1, v.2)) := by
  intro pre determined w
  obtain ⟨b,hb⟩ := v2_blinding_residue_ring_perfectly_simulated s shiftDeg qs xs hqs hqz hv (rd w)
  obtain ⟨l,hl⟩ := logUp_joint_rank15 u k ((lookupLimbDet_eq u) ▸ hu) hk (ld w)
  let e := equivProd b l
  have he a : pre w a = simulatedPrefix (e.toFun a) := Prod.ext (hb a.1) (hl a.2)
  let line (a) : SimpleEquiv (ι → E) (ι → E) :=
    ⟨maskLine β (word w a), unmaskLine β (word w a), unmaskLine_maskLine β hβ _, maskLine_unmaskLine β hβ _⟩
  refine ⟨equivOver e line, fun c => ?_⟩
  have hp := lookup_product_retry_public table (query w) padding (satisfying w) α
  by_cases hit : α ∈ lookupPoles table padding
  · simp only [hit, hp.mpr hit, ite_true]
  · have hn := mt hp.mp hit
    simp only [hn,hit,ite_false]
    have hm := v2_mask_line_view_eq_sim β hβ ℓ openings (word w c.1) c.2
    obtain ⟨hc,ho,hf⟩ := determined w c.1
    rw [hc, funext ho] at hm
    change some (_,_,_,_) = some (maskLineSim β ℓ openings (σ (simulatedPrefix (e.toFun c.1)))
      (o (simulatedPrefix (e.toFun c.1))) (maskLine β (word w c.1) c.2),_,_,_)
    rw [hm, hf, he]
    rfl

#print axioms shared_tape_four_view_simulation

/-! ## Coordinates for every quotient-ring fold -/

abbrev FixedList (A : Type) (n : Nat) := {p : List A // p.length = n}

private def fixedCoordinates {A : Type} (n : Nat) : SimpleEquiv (FixedList A n) (Fin n → A) where
  toFun l i := l.val[i.val]'(l.property.symm ▸ i.isLt)
  invFun f := ⟨List.ofFn f, List.length_ofFn⟩
  left_inv l := by
    apply Subtype.ext
    apply List.ext_getElem (by simp [l.property])
    intro i ha hb
    simp only [List.getElem_ofFn]
  right_inv f := by funext i; simp only [List.getElem_ofFn]

abbrev FiberResidues (xs : List E) (n : Nat) :=
  {rs : List (List E) // rs.length = xs.length ∧ ∀ r ∈ rs, r.length = n}

private def rowsAsFunction (xs : List E) (hn : xs.length = 5) (n : Nat) :
    SimpleEquiv (FiberResidues xs n) (Fin 5 → FixedList E n) where
  toFun rs i :=
    let h : i.val < rs.val.length := by rw [rs.property.1, hn]; exact i.isLt
    ⟨rs.val[i.val], rs.property.2 _ (List.getElem_mem h)⟩
  invFun f := ⟨List.ofFn (fun i => (f i).val), by
    refine ⟨List.length_ofFn.trans hn.symm, ?_⟩
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact (f i).property⟩
  left_inv rs := by
    apply Subtype.ext
    apply List.ext_getElem (by simp only [List.length_ofFn, rs.property.1, hn])
    intro i ha hb
    simp only [List.getElem_ofFn]
  right_inv f := by funext i; apply Subtype.ext; simp only [List.getElem_ofFn]

/-- Monomial coefficients indexed by their low bit first. At width `s+1`
    fixing the first bit selects the even or odd half-polynomial. -/
abbrev CoeffIndex : Nat → Type
  | 0 => Unit
  | s+1 => Bool × CoeffIndex s

abbrev FiberPoly (s : Nat) := CoeffIndex s → QuinticGoldilocks

private def joinParts {s : Nat} (f g : FiberPoly s) : FiberPoly (s+1) :=
  fun (b,i) => if b then g i else f i

def fiberEval : (s : Nat) → E → FiberPoly s → E
  | 0, _, p => p ()
  | s+1, x, p => add (fiberEval s (mul x x) (fun i => p (false,i)))
      (mul x (fiberEval s (mul x x) (fun i => p (true,i))))

/-- Multiplication by the indeterminate in the fiber quotient.
    At width one the indeterminate is the field element itself. -/
def fiberShift : (s : Nat) → E → FiberPoly s → FiberPoly s
  | 0, x, p => fun i => mul x (p i)
  | s+1, x, p => joinParts (fiberShift s (mul x x) (fun i => p (true,i))) (fun i => p (false,i))

private def fiberConst : (s : Nat) → E → FiberPoly s
  | 0, c => fun _ => c
  | s+1, c => joinParts (fiberConst s c) (fun _ => zero)

private theorem fiberEval_zero (s : Nat) (x : E) : fiberEval s x (fun _ => zero) = zero := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih => simp only [fiberEval, ih]; constructive_ring

private theorem fiberEval_const (s : Nat) (x c : E) : fiberEval s x (fiberConst s c) = c := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih =>
    change add (fiberEval s _ (fiberConst s c)) (mul x (fiberEval s _ (fun _ => zero))) = c
    rw [ih, fiberEval_zero]; constructive_ring

private theorem fiberEval_add (s : Nat) (x : E) (p q : FiberPoly s) :
    fiberEval s x (fun i => add (p i) (q i)) = add (fiberEval s x p) (fiberEval s x q) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih => simp only [fiberEval, ih]; constructive_ring

private theorem fiberEval_scale (s : Nat) (x c : E) (p : FiberPoly s) :
    fiberEval s x (fun i => mul c (p i)) = mul c (fiberEval s x p) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih => simp only [fiberEval, ih]; constructive_ring

private theorem fiberEval_sub (s : Nat) (x : E) (p q : FiberPoly s) :
    fiberEval s x (fun i => sub (p i) (q i)) = sub (fiberEval s x p) (fiberEval s x q) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih => simp only [fiberEval, ih]; constructive_ring

theorem fiberEval_shift (s : Nat) (x : E) (p : FiberPoly s) :
    fiberEval s x (fiberShift s x p) = mul x (fiberEval s x p) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih =>
    change add (fiberEval s _ (fiberShift s _ _)) (mul x (fiberEval s _ _)) =
      mul x (add _ (mul x _))
    let f := fiberEval s (mul x x) (fun i => p (false,i))
    let g := fiberEval s (mul x x) (fun i => p (true,i))
    rw [ih]
    change add (mul (mul x x) g) (mul x f) = mul x (add f (mul x g))
    constructive_ring

structure FiberFoldCoins where
  theta : E
  alpha : E
  beta : E

private def blendShift (s : Nat) (x : E) (c : FiberFoldCoins) (h : FiberPoly s) : FiberPoly s :=
  fun i => add (mul c.alpha (h i)) (mul c.beta (fiberShift s x h i))

private theorem eval_blendShift (s : Nat) (x : E) (c : FiberFoldCoins) (h : FiberPoly s) :
    fiberEval s x (blendShift s x c h) =
      mul (add c.alpha (mul c.beta x)) (fiberEval s x h) := by
  unfold blendShift
  rw [fiberEval_add s x (fun i => mul c.alpha (h i)) (fun i => mul c.beta (fiberShift s x h i)),
    fiberEval_scale, fiberEval_scale, fiberEval_shift]
  constructive_ring

/-- PCS fold `G + (alpha + beta Y)(F + theta G)` reduced on the child fiber. -/
def fiberFold (s : Nat) (x : E) (c : FiberFoldCoins) (p : FiberPoly (s+1)) : FiberPoly s :=
  let h i := add (p (false,i)) (mul c.theta (p (true,i)))
  fun i => add (p (true,i)) (blendShift s (mul x x) c h i)

private def stepChange (s : Nat) (x : E) (c : FiberFoldCoins) :
    SimpleEquiv (FiberPoly (s+1)) (FiberPoly s × FiberPoly s) where
  toFun p := (fiberFold s x c p, fun i => add (p (false,i)) (mul c.theta (p (true,i))))
  invFun v :=
    let g i := sub (v.1 i) (blendShift s (mul x x) c v.2 i)
    joinParts (fun i => sub (v.2 i) (mul c.theta (g i))) g
  left_inv p := by
    funext ⟨b,i⟩
    let h j := add (p (false,j)) (mul c.theta (p (true,j)))
    let a := blendShift s (mul x x) c h i
    cases b
    · change sub (add (p (false,i)) (mul c.theta (p (true,i)))) (mul c.theta (sub (add (p (true,i)) a) a)) = _
      constructive_ring
    · change sub (add (p (true,i)) a) a = p (true,i)
      constructive_ring
  right_inv v := by
    let g i := sub (v.1 i) (blendShift s (mul x x) c v.2 i)
    have h : (fun i => add (sub (v.2 i) (mul c.theta (g i))) (mul c.theta (g i))) = v.2 := by
      funext i; constructive_ring
    apply Prod.ext
    · change (fun i => add (g i) (blendShift s (mul x x) c
        (fun j => add (sub (v.2 j) (mul c.theta (g j))) (mul c.theta (g j))) i)) = v.1
      rw [show (fun i => add (sub (v.2 i) (mul c.theta (g i))) (mul c.theta (g i))) = v.2 from h]
      funext i; dsimp only [g]; constructive_ring
    · exact h

private def centered (s : Nat) (x : E) := {h : FiberPoly s // fiberEval s x h = zero}

private def splitEvaluation (s : Nat) (x : E) : SimpleEquiv (FiberPoly s) (E × centered s x) where
  toFun h := (fiberEval s x h, ⟨fun i => sub (h i) (fiberConst s (fiberEval s x h) i), by
    rw [fiberEval_sub, fiberEval_const]; constructive_ring⟩)
  invFun v := fun i => add (v.2.val i) (fiberConst s v.1 i)
  left_inv h := by funext i; dsimp only; constructive_ring
  right_inv v := by
    have ev : fiberEval s x (fun i => add (v.2.val i) (fiberConst s v.1 i)) = v.1 := by
      rw [fiberEval_add, fiberEval_const, v.2.property]; constructive_ring
    exact Prod.ext ev (Subtype.ext (by funext i; dsimp only; rw [ev]; constructive_ring))

/-- Swap the child evaluation and the evaluation of its auxiliary polynomial
    for the parent evaluation and the even-part evaluation. -/
private def scalarStep (x e theta : E) (hx : x ≠ zero) : SimpleEquiv (E × E) (E × E) where
  toFun v :=
    let g := sub v.1 (mul e v.2)
    let f := sub v.2 (mul theta g)
    (add f (mul x g), f)
  invFun t :=
    let g := mul (LawfulField.inv x) (sub t.1 t.2)
    let h := add t.2 (mul theta g)
    (add g (mul e h), h)
  left_inv v := by
    let g := sub v.1 (mul e v.2)
    let f := sub v.2 (mul theta g)
    have hg : mul (LawfulField.inv x) (sub (add f (mul x g)) f) = g := by
      calc
        _ = mul (mul (LawfulField.inv x) x) g := by constructive_ring
        _ = _ := by rw [LawfulField.inv_mul_cancel hx]; constructive_ring
    dsimp only
    change (add _ (mul e _), add f (mul theta (mul (LawfulField.inv x) (sub (add f (mul x g)) f)))) = v
    rw [hg]
    apply Prod.ext <;> dsimp only [f,g] <;> constructive_ring
  right_inv t := by
    let g := mul (LawfulField.inv x) (sub t.1 t.2)
    let h := add t.2 (mul theta g)
    have hxg : mul x g = sub t.1 t.2 := by
      dsimp only [g]; rw [← LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hx, LawfulCommRing.one_mul]
    change (add (sub h (mul theta (sub (add g (mul e h)) (mul e h))))
      (mul x (sub (add g (mul e h)) (mul e h))), _) = t
    rw [show sub (add g (mul e h)) (mul e h) = g by constructive_ring, hxg]
    apply Prod.ext
    · change add (sub (add t.2 (mul theta g)) (mul theta g)) (sub t.1 t.2) = t.1
      constructive_ring
    · change sub (add t.2 (mul theta g)) (mul theta g) = t.2
      constructive_ring

private theorem scalarStep_eval (s : Nat) (x : E) (hx : x ≠ zero) (c : FiberFoldCoins)
    (p : FiberPoly (s+1)) :
    let y := mul x x
    let t := (stepChange s x c).toFun p
    (scalarStep x (add c.alpha (mul c.beta y)) c.theta hx).toFun
        (fiberEval s y t.1, fiberEval s y t.2) =
      (fiberEval (s+1) x p, fiberEval s y (fun i => p (false,i))) := by
  let y := mul x x
  let f (i : CoeffIndex s) := p (false,i)
  let g (i : CoeffIndex s) := p (true,i)
  let h i := add (f i) (mul c.theta (g i))
  let e := add c.alpha (mul c.beta y)
  have hh : fiberEval s y h = add (fiberEval s y f) (mul c.theta (fiberEval s y g)) :=
    (fiberEval_add s y f (fun i => mul c.theta (g i))).trans (congrArg (add _) (fiberEval_scale ..))
  have hn : fiberEval s y (fiberFold s x c p) = add (fiberEval s y g) (mul e (fiberEval s y h)) :=
    (fiberEval_add s y g (blendShift s y c h)).trans (congrArg (add _) (eval_blendShift ..))
  change (scalarStep x e c.theta hx).toFun (fiberEval s y (fiberFold s x c p), fiberEval s y h) =
    (add (fiberEval s y f) (mul x (fiberEval s y g)), fiberEval s y f)
  rw [hn, hh]
  generalize fiberEval s y f = a
  generalize fiberEval s y g = b
  apply Prod.ext <;> dsimp only [scalarStep] <;> constructive_ring

/-- One entry for each even-part evaluation, in chronological order. -/
abbrev FoldValues : Nat → Type
  | 0 => Unit
  | n+1 => E × FoldValues n

def fiberTrace : (s : Nat) → E → (Nat → FiberFoldCoins) → FiberPoly s → E × FoldValues s
  | 0, x, _, p => (fiberEval 0 x p, ())
  | s+1, x, cs, p =>
    (fiberEval (s+1) x p, fiberEval s (mul x x) (fun i => p (false,i)),
     (fiberTrace s (mul x x) (fun i => cs (i+1)) (fiberFold s x (cs 0) p)).2)

private def joinStepCoordinates {B C D : Type} (sc : SimpleEquiv (E × E) (E × E)) :
    SimpleEquiv (((E × B) × C) × (E × D)) ((E × E × B) × D × C) where
  toFun t := let v := sc.toFun (t.1.1.1,t.2.1)
             ((v.1, v.2, t.1.1.2), t.2.2, t.1.2)
  invFun t := let v := sc.invFun (t.1.1,t.1.2.1)
              (((v.1,t.1.2.2),t.2.2),v.2,t.2.1)
  left_inv t := by dsimp only; rw [sc.left_inv]
  right_inv t := by dsimp only; rw [sc.right_inv]

private theorem square_ne_zero (x : E) (hx : x ≠ zero) : mul x x ≠ zero := by
  have h := fpow_ne_zero hx 2
  simpa only [fpow.public_eqs, LawfulCommRing.mul_one, LawfulCommRing.one_mul] using h

/-- Unobserved polynomial directions at each fold of a single point fiber. -/
def FiberSlack : (s : Nat) → E → Type
  | 0, _ => Unit
  | s+1, x => centered s (mul x x) × FiberSlack s (mul x x)

noncomputable def fiberCoordinates : (s : Nat) → (x : E) → x ≠ zero → (Nat → FiberFoldCoins) →
    SimpleEquiv (FiberPoly s) ((E × FoldValues s) × FiberSlack s x)
  | 0, _, _, _ => ⟨fun p => ((p (),()),()), fun v _ => v.1.1,
      fun p => by funext i; cases i; rfl, fun ⟨⟨_,⟨⟩⟩,⟨⟩⟩ => rfl⟩
  | s+1, x, hx, cs =>
    let y := mul x x
    let c := cs 0
    let e := fiberCoordinates s y (square_ne_zero x hx) (fun i => cs (i+1))
    (postProd (stepChange s x c) e (splitEvaluation s y)).trans
      (joinStepCoordinates (scalarStep x (add c.alpha (mul c.beta y)) c.theta hx))

set_option maxHeartbeats 1200000 in
/-- Lemma V2.3(b) on the entire sequence of quotient folds. The projection
    onto the original point evaluation and one even-part evaluation per fold
    is a coordinate projection of an explicit bijection, for every fixed
    challenge sequence. -/
theorem all_fold_fiber_coordinates (s : Nat) (x : E) (hx : x ≠ zero) (cs : Nat → FiberFoldCoins)
    (p : FiberPoly s) : ((fiberCoordinates s x hx cs).toFun p).1 = fiberTrace s x cs p := by
  induction s generalizing x cs with
  | zero => rfl
  | succ s ih =>
    let y := mul x x
    let c := cs 0
    let step := stepChange s x c
    let e := fiberCoordinates s y (square_ne_zero x hx) (fun i => cs (i+1))
    let sc := scalarStep x (add c.alpha (mul c.beta y)) c.theta hx
    let t := step.toFun p
    have he (q : FiberPoly s) : (e.toFun q).1 = fiberTrace s y (fun i => cs (i+1)) q := ih ..
    simp only [fiberCoordinates, SimpleEquiv.trans, postProd_apply]
    change ( (sc.toFun (((e.toFun t.1).1.1), fiberEval s y t.2)).1,
      (sc.toFun (((e.toFun t.1).1.1), fiberEval s y t.2)).2, (e.toFun t.1).1.2) = _
    rw [he]
    have ev (q : FiberPoly s) : (fiberTrace s y (fun i => cs (i+1)) q).1 = fiberEval s y q := by
      cases s <;> rfl
    rw [ev]
    have hsc : sc.toFun (fiberEval s y t.1, fiberEval s y t.2) =
        (fiberEval (s+1) x p, fiberEval s y (fun i => p (false,i))) :=
      scalarStep_eval s x hx c p
    rw [hsc]
    rfl

#print axioms all_fold_fiber_coordinates

/-! ## Ordinary polynomials and the canonical binomial remainder -/

private def splitCoefficients : List E → List E × List E
  | [] => ([],[])
  | [a] => ([a],[])
  | a :: b :: cs =>
    let v := splitCoefficients cs
    (a :: v.1,b :: v.2)

private theorem interleaveShape (a b : List E) (h : a.length = b.length) :
    (hemInterleave a b).length = a.length + b.length ∧ splitCoefficients (hemInterleave a b) = (a,b) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rw [hemInterleave_nil_left]; exact ⟨rfl,rfl⟩
    | cons _ _ => exact False.elim ((Nat.noConfusion h))
  | cons a as ih =>
    cases b with
    | nil => exact False.elim (Nat.noConfusion h)
    | cons b bs =>
      obtain ⟨hl,hs⟩ := ih bs (Nat.succ.inj h)
      rw [hemInterleave_cons_cons]
      constructor
      · change (hemInterleave as bs).length + 1 + 1 = _
        rw [hl]; simp only [List.length_cons, Nat.succ_add, Nat.add_succ]
      · exact congrArg (fun t : List E × List E => (a :: t.1,b :: t.2)) hs

private theorem splitShape : ∀ (n : Nat) (p : List E), p.length = n+n →
    (splitCoefficients p).1.length = n ∧ (splitCoefficients p).2.length = n ∧
      hemInterleave (splitCoefficients p).1 (splitCoefficients p).2 = p
  | 0, [], _ => by simp only [splitCoefficients, hemInterleave_nil_left]; decide
  | 0, _ :: _, h => by simp at h
  | n+1, [], h => by simp at h
  | n+1, [_], h => by simp at h <;> omega
  | n+1, a :: b :: p, h => by
    have hl : p.length = n+n := by simp only [List.length_cons] at h; omega
    obtain ⟨h₁,h₂,h₃⟩ := splitShape n p hl
    simp only [splitCoefficients, hemInterleave_cons_cons]
    change (_+1=n+1 ∧ _+1=n+1 ∧ a :: b :: hemInterleave _ _ = _)
    exact ⟨congrArg Nat.succ h₁, congrArg Nat.succ h₂, congrArg (fun q => a :: b :: q) h₃⟩

private def splitRows (n : Nat) : SimpleEquiv (FixedList E (n+n)) (FixedList E n × FixedList E n) where
  toFun p := (⟨(splitCoefficients p.val).1, (splitShape n p.val p.property).1⟩,
    ⟨(splitCoefficients p.val).2, (splitShape n p.val p.property).2.1⟩)
  invFun v := ⟨hemInterleave v.1.val v.2.val, (interleaveShape _ _ (v.1.property.trans v.2.property.symm)).1.trans
    (by rw [v.1.property, v.2.property])⟩
  left_inv p := Subtype.ext (splitShape n p.val p.property).2.2
  right_inv v := by
    have e := (interleaveShape _ _ (v.1.property.trans v.2.property.symm)).2
    exact Prod.ext (Subtype.ext (congrArg Prod.fst e)) (Subtype.ext (congrArg Prod.snd e))

private def halves (s : Nat) : SimpleEquiv (FiberPoly (s+1)) (FiberPoly s × FiberPoly s) where
  toFun p := (fun i => p (false,i),fun i => p (true,i))
  invFun v := joinParts v.1 v.2
  left_inv p := by funext ⟨b,i⟩; cases b <;> rfl
  right_inv _ := rfl

private def lengthCast {A : Type} {m n : Nat} (h : m = n) : SimpleEquiv (FixedList A m) (FixedList A n) where
  toFun p := ⟨p.val,p.property.trans h⟩
  invFun p := ⟨p.val,p.property.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem twiceWidth (s : Nat) : 2^s + 2^s = 2^(s+1) := by rw [Nat.pow_succ, Nat.mul_two]

/-- Serialize a fiber as its ordinary little-endian monomial coefficient
    list. The inverse splits alternating coefficients at each level. -/
noncomputable def fiberCoefficientList : (s : Nat) → SimpleEquiv (FiberPoly s) (FixedList E (2^s))
  | 0 => ⟨fun p => ⟨[p ()],rfl⟩, fun v _ => v.val.headD zero,
      fun p => by funext i; cases i; rfl, fun ⟨l,h⟩ => by
        cases l with
        | nil => exact False.elim (Nat.noConfusion (show 0 = 1 from h))
        | cons a t =>
          have ht : t = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at h; change _ = 1 at h; omega)
          subst t; rfl⟩
  | s+1 => ((postProd (halves s) (fiberCoefficientList s) (fiberCoefficientList s)).trans
      (splitRows (2^s)).symm).trans (lengthCast (twiceWidth s))

private theorem eval_interleaved (x : E) (as bs : List E) (h : as.length = bs.length) :
    RoundPoly.evalCoeffs (hemInterleave as bs) x =
      add (RoundPoly.evalCoeffs as (mul x x)) (mul x (RoundPoly.evalCoeffs bs (mul x x))) := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => rw [hemInterleave_nil_left]; change zero = add zero (mul x zero); constructive_ring
    | cons _ _ => exact False.elim (Nat.noConfusion h)
  | cons a as ih =>
    cases bs with
    | nil => exact False.elim (Nat.noConfusion h)
    | cons b bs =>
      rw [hemInterleave_cons_cons]
      change add a (mul x (add b (mul x (RoundPoly.evalCoeffs (hemInterleave as bs) x)))) = _
      rw [ih bs (Nat.succ.inj h)]
      simp only [RoundPoly.evalCoeffs_cons]
      constructive_ring

theorem fiberCoefficientList_eval (s : Nat) (x : E) (p : FiberPoly s) :
    RoundPoly.evalCoeffs ((fiberCoefficientList s).toFun p).val x = fiberEval s x p := by
  induction s generalizing x with
  | zero => change add (p ()) (mul x zero) = p (); constructive_ring
  | succ s ih =>
    let a := (fiberCoefficientList s).toFun (fun i => p (false,i))
    let b := (fiberCoefficientList s).toFun (fun i => p (true,i))
    simp only [fiberCoefficientList, SimpleEquiv.trans, postProd_apply]
    change RoundPoly.evalCoeffs (hemInterleave a.val b.val) x = _
    rw [eval_interleaved x _ _ (a.property.trans b.property.symm)]
    change add (RoundPoly.evalCoeffs ((fiberCoefficientList s).toFun _).val _) (mul x (RoundPoly.evalCoeffs ((fiberCoefficientList s).toFun _).val _)) = _
    rw [ih,ih]; rfl

private theorem squareWidth (s : Nat) (x : E) :
    fpow (mul x x) (2^s) = fpow x (2^(s+1)) := by
  rw [← twiceWidth, fpow_add, fpow_mul_base]

private theorem eval_splitCoefficients (x : E) : ∀ p : List E,
    RoundPoly.evalCoeffs p x = add (RoundPoly.evalCoeffs (splitCoefficients p).1 (mul x x))
      (mul x (RoundPoly.evalCoeffs (splitCoefficients p).2 (mul x x)))
  | [] => by change zero = add zero (mul x zero); constructive_ring
  | [a] => by simp only [RoundPoly.evalCoeffs, splitCoefficients]; constructive_ring
  | a :: b :: p => by
    simp only [RoundPoly.evalCoeffs_cons, splitCoefficients]
    rw [eval_splitCoefficients x p]
    constructive_ring

private theorem shift_at_fiber (s : Nat) (x y : E) (h : fpow x (2^s) = fpow y (2^s))
    (p : FiberPoly s) : fiberEval s y (fiberShift s x p) = mul y (fiberEval s y p) := by
  induction s generalizing x y with
  | zero =>
    have e : x = y := by simpa only [Nat.pow_zero, fpow.public_eqs, LawfulCommRing.mul_one] using h
    subst y; rfl
  | succ s ih =>
    let even := fiberEval s (mul y y) (fun i => p (false,i))
    let odd := fiberEval s (mul y y) (fun i => p (true,i))
    have hs : fpow (mul x x) (2^s) = fpow (mul y y) (2^s) := by simpa only [squareWidth] using h
    change add (fiberEval s (mul y y) (fiberShift s (mul x x) _)) (mul y even) = mul y (add even (mul y odd))
    rw [ih _ _ hs]
    change add (mul (mul y y) odd) (mul y even) = mul y (add even (mul y odd))
    constructive_ring

/-- Reduce a polynomial of any degree on the fiber by splitting its ordinary
    monomial coefficients into even and odd halves down to scalar evaluations. -/
def polynomialFiber : (s : Nat) → E → List E → FiberPoly s
  | 0,x,p => fun _ => RoundPoly.evalCoeffs p x
  | s+1,x,p => joinParts (polynomialFiber s (mul x x) (splitCoefficients p).1)
      (polynomialFiber s (mul x x) (splitCoefficients p).2)

private theorem polynomialFiber_eval (s : Nat) (x y : E) (h : fpow x (2^s) = fpow y (2^s)) (p : List E) :
    fiberEval s y (polynomialFiber s x p) = RoundPoly.evalCoeffs p y := by
  induction s generalizing x y p with
  | zero =>
    have e : x = y := by simpa only [Nat.pow_zero, fpow.public_eqs, LawfulCommRing.mul_one] using h
    subst y; rfl
  | succ s ih =>
    have hs : fpow (mul x x) (2^s) = fpow (mul y y) (2^s) := by simpa only [squareWidth] using h
    change add (fiberEval s (mul y y) (polynomialFiber s (mul x x) _))
      (mul y (fiberEval s (mul y y) (polynomialFiber s (mul x x) _))) = _
    rw [ih _ _ hs, ih _ _ hs]; exact (eval_splitCoefficients y p).symm

private theorem equal_on_fiber (s : Nat) (hs : s ≤ 32) (x : E) (hx : x ≠ zero)
    (p q : List E) (hp : p.length = 2^s) (hq : q.length = 2^s)
    (he : ∀ y ∈ fiberRoots s x, RoundPoly.evalCoeffs p y = RoundPoly.evalCoeffs q y) : p = q := by
  let dom := fiberRoots s x
  have nd := fiberRoots_nodup s hs hx
  have hl := fiberRoots_length s x
  have hem : dom.map (RoundPoly.evalCoeffs p) = dom.map (RoundPoly.evalCoeffs q) := List.map_congr_left he
  exact (newtonInterp_eval dom p nd (hp.trans hl.symm)).symm.trans
    ((congrArg (newtonInterp dom) hem).trans (newtonInterp_eval dom q nd (hq.trans hl.symm)))

/-- The fiber coordinate representation is exactly the canonical remainder
    returned by the binomial division used in the original CRT theorem. -/
theorem polynomialFiber_remainder (s : Nat) (hs : s ≤ 32) (x : E) (hx : x ≠ zero) (p : List E) :
    ((fiberCoefficientList s).toFun (polynomialFiber s x p)).val =
      (divModBinomial (2^s-1) (fpow x (2^s)) p).1 := by
  have hlen : 2^s-1+1 = 2^s := by have := Nat.two_pow_pos s; omega
  apply equal_on_fiber s hs x hx _ _ ((fiberCoefficientList s).toFun _).property
      ((divModBinomial_rem_length ..).trans hlen)
  intro y hy
  have root := fiberRoots_pow s hs x hy
  rw [fiberCoefficientList_eval, polynomialFiber_eval s x y root.symm, evalCoeffs_divModBinomial_at_root]
  rw [hlen]; exact root

/-- The polynomial computed in pcs.rs, with high zero coefficients trimmed. -/
def nextFoldPolynomial (c : FiberFoldCoins) (p : List E) : List E :=
  let f := (splitCoefficients p).1
  let g := (splitCoefficients p).2
  let h := pAdd f (pScale c.theta g)
  pAdd g (pAdd (pScale c.alpha h) (zero :: pScale c.beta h))

theorem polynomialFiber_fold (s : Nat) (hs : s ≤ 32) (x : E) (hx : x ≠ zero)
    (c : FiberFoldCoins) (p : List E) :
    fiberFold s x c (polynomialFiber (s+1) x p) =
      polynomialFiber s (mul x x) (nextFoldPolynomial c p) := by
  let z := mul x x
  let f := polynomialFiber s z (splitCoefficients p).1
  let g := polynomialFiber s z (splitCoefficients p).2
  let h i := add (f i) (mul c.theta (g i))
  let e := fiberCoefficientList s
  suffices eq : (e.toFun (fiberFold s x c (polynomialFiber (s+1) x p))).val =
      (e.toFun (polynomialFiber s z (nextFoldPolynomial c p))).val by
    have h' := congrArg e.invFun (Subtype.ext eq)
    simpa only [e.left_inv] using h'
  apply equal_on_fiber s hs z (square_ne_zero x hx) _ _ (e.toFun _).property (e.toFun _).property
  intro y hy
  have root := (fiberRoots_pow s hs z hy).symm
  simp only [e,fiberCoefficientList_eval]
  rw [polynomialFiber_eval s z y root]
  change fiberEval s y (fun i => add (g i) (blendShift s z c h i)) = _
  rw [fiberEval_add s y g (blendShift s z c h)]
  have bh : fiberEval s y (blendShift s z c h) =
      add (mul c.alpha (fiberEval s y h)) (mul c.beta (mul y (fiberEval s y h))) := by
    unfold blendShift
    rw [fiberEval_add s y (fun i => mul c.alpha (h i)) (fun i => mul c.beta (fiberShift s z h i)),
      fiberEval_scale, fiberEval_scale, shift_at_fiber s z y root]
  rw [bh]
  have vh : fiberEval s y h = add (fiberEval s y f) (mul c.theta (fiberEval s y g)) :=
    (fiberEval_add s y f (fun i => mul c.theta (g i))).trans (congrArg _ (fiberEval_scale ..))
  rw [vh, show fiberEval s y f = _ from polynomialFiber_eval s z y root (splitCoefficients p).1,
    show fiberEval s y g = _ from polynomialFiber_eval s z y root (splitCoefficients p).2]
  simp only [nextFoldPolynomial, evalCoeffs_pAdd, evalCoeffs_pScale, RoundPoly.evalCoeffs_cons]
  constructive_ring

/-- Direct observations of the ordinary polynomial folds, including overflow
    coefficients in each next polynomial. -/
def polynomialFoldTrace : (s : Nat) → E → (Nat → FiberFoldCoins) → List E → E × FoldValues s
  | 0,x,_,p => (RoundPoly.evalCoeffs p x,())
  | s+1,x,cs,p => (RoundPoly.evalCoeffs p x,
      RoundPoly.evalCoeffs (splitCoefficients p).1 (mul x x),
      (polynomialFoldTrace s (mul x x) (fun i => cs (i+1)) (nextFoldPolynomial (cs 0) p)).2)

theorem fiberTrace_of_polynomial (s : Nat) (hs : s ≤ 32) (x : E) (hx : x ≠ zero)
    (cs : Nat → FiberFoldCoins) (p : List E) :
    fiberTrace s x cs (polynomialFiber s x p) = polynomialFoldTrace s x cs p := by
  induction s generalizing x cs p with
  | zero => rfl
  | succ s ih =>
    have hk : s ≤ 32 := by omega
    change (fiberEval (s+1) x (polynomialFiber (s+1) x p),
      fiberEval s (mul x x) (polynomialFiber s (mul x x) _),
      (fiberTrace s (mul x x) _ (fiberFold s x (cs 0) (polynomialFiber (s+1) x p))).2) = _
    rw [polynomialFiber_eval _ _ _ rfl, polynomialFiber_eval _ _ _ rfl, polynomialFiber_fold s hk x hx,
      ih hk _ (square_ne_zero x hx)]
    rfl

#print axioms polynomialFiber_remainder
#print axioms fiberTrace_of_polynomial

/-! ## The projected Stage-0 transcript -/

/-- Five scalars per fold, in the order the folds execute. -/
abbrev FoldBlocks : Nat → Type
  | 0 => Unit
  | n+1 => FiveFoldCells × FoldBlocks n

def gatherByRound : (s : Nat) → SimpleEquiv (Fin 5 → FoldValues s) (FoldBlocks s)
  | 0 => ⟨fun _ => (), fun _ _ => (), fun _ => rfl, fun _ => rfl⟩
  | s+1 =>
    let v := fixedCoordinates (A := E) 5
    let t := gatherByRound s
    { toFun := fun p => (v.invFun (fun i => (p i).1), t.toFun (fun i => (p i).2))
      invFun := fun a i => (v.toFun a.1 i, t.invFun a.2 i)
      left_inv := fun p => by dsimp only; rw [v.right_inv, t.left_inv]
      right_inv := fun a => by dsimp only; rw [v.left_inv, t.right_inv] }

private noncomputable def fiveCoordinates (s : Nat) (xs : List E) (hl : xs.length = 5)
    (hx : ∀ x ∈ xs, x ≠ zero) (cs : Nat → FiberFoldCoins) :
    SimpleEquiv (FiberResidues xs (2^s)) ((FiveFoldCells × FoldBlocks s) ×
      ((i : Fin 5) → FiberSlack s (xs[i.val]'(hl.symm ▸ i.isLt)))) :=
  let row := rowsAsFunction xs hl (2^s)
  let e (i : Fin 5) := (fiberCoefficientList s).symm.trans
    (fiberCoordinates s (xs[i.val]'(hl.symm ▸ i.isLt)) (hx _ (List.getElem_mem _)) cs)
  let v := fixedCoordinates (A := E) 5
  let g := gatherByRound s
  { toFun := fun r =>
      let t i := (e i).toFun (row.toFun r i)
      ((v.invFun (fun i => (t i).1.1), g.toFun (fun i => (t i).1.2)),fun i => (t i).2)
    invFun := fun t => row.invFun fun i => (e i).invFun ((v.toFun t.1.1 i,g.invFun t.1.2 i), t.2 i)
    left_inv := fun r => by
      dsimp only; simp only [v.right_inv, g.left_inv]
      have h : (fun i => (e i).invFun ((e i).toFun (row.toFun r i))) = row.toFun r :=
        funext fun i => (e i).left_inv _
      exact (congrArg row.invFun h).trans (row.left_inv r)
    right_inv := fun t => by dsimp only; simp only [row.right_inv, (e _).right_inv, v.left_inv, g.right_inv] }

private def paddedRow (n : Nat) (r : List E) : FixedList E n :=
  ⟨List.ofFn (fun i : Fin n => r.getD i.val zero), List.length_ofFn⟩

private theorem paddedRow_exact {n : Nat} (p : FixedList E n) : paddedRow n p.val = p := by
  apply Subtype.ext
  apply List.ext_getElem (by simp [paddedRow,p.property])
  intro i hi hj
  simp only [paddedRow, List.getElem_ofFn, List.getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-- Evaluate the real masked residue at each of the five points, and follow
    the even halves through every successive quotient fold. -/
noncomputable def projectedFibers (s : Nat) (xs : List E) (cs : Nat → FiberFoldCoins)
    (rs : List (List E)) : FiveFoldCells × FoldBlocks s :=
  let t (i : Fin 5) := fiberTrace s (xs.getD i.val zero) cs
    ((fiberCoefficientList s).invFun (paddedRow (2^s) (rs.getD i.val [])))
  ((fixedCoordinates 5).invFun (fun i => (t i).1), (gatherByRound s).toFun fun i => (t i).2)

private theorem eval_addRows (x : E) (a b : List E) (h : a.length = b.length) :
    RoundPoly.evalCoeffs (ZkHem.vadd a b) x = add (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp only [ZkHem.vadd.public_eqs]; change (zero : E) = add zero zero; constructive_ring
    | cons _ _ => exact False.elim (Nat.noConfusion h)
  | cons a as ih =>
    cases b with
    | nil => exact False.elim (Nat.noConfusion h)
    | cons b bs =>
      simp only [ZkHem.vadd.public_eqs]
      change add (add a b) (mul x (RoundPoly.evalCoeffs (ZkHem.vadd as bs) x)) = _
      rw [ih bs (Nat.succ.inj h)]
      simp only [RoundPoly.evalCoeffs_cons]
      constructive_ring

noncomputable def fiberRemainder (s : Nat) (x : E) (p : List E) :=
  (divModBinomial (2^s-1) (fpow x (2^s)) p).1

private theorem addRemainders (s : Nat) (hs : s ≤ 32) (x : E) (hx : x ≠ zero) (p b : List E) :
    ZkHem.vadd (fiberRemainder s x p) (fiberRemainder s x b) = fiberRemainder s x (pAdd p b) := by
  have hlen : 2^s-1+1 = 2^s := by have := Nat.two_pow_pos s; omega
  have len (q : List E) : (fiberRemainder s x q).length = 2^s := (divModBinomial_rem_length ..).trans hlen
  have eq := (len p).trans (len b).symm
  apply equal_on_fiber s hs x hx _ _ ((ZkHem.vadd_length _ _ eq).trans (len b)) (len _)
  intro y hy
  have r : fpow y (2^s-1+1) = fpow x (2^s) := hlen ▸ fiberRoots_pow s hs x hy
  rw [eval_addRows _ _ _ eq]
  simp only [fiberRemainder,evalCoeffs_divModBinomial_at_root _ _ _ r,evalCoeffs_pAdd]

private theorem addRemainderRows (s : Nat) (hs : s ≤ 32) (p b : List E) (xs : List E)
    (hx : ∀ x ∈ xs, x ≠ zero) :
    vaddResidues (xs.map fun x => fiberRemainder s x p) (xs.map fun x => fiberRemainder s x b) =
      xs.map fun x => fiberRemainder s x (pAdd p b) := by
  induction xs with
  | nil => simp only [List.map_nil, vaddResidues.public_eqs]
  | cons x xs ih =>
    simp only [List.map_cons, vaddResidues.public_eqs, addRemainders s hs x (hx x List.mem_cons_self)]
    rw [ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))]

/-- The shared-tape fold coordinates in the simulator agree with direct
    ordinary-polynomial folds of the masked source, for every lower polynomial
    and every actual vector of high base-field blinder coefficients. -/
theorem projectedFibers_masked_polynomial (s shiftDeg : Nat) (hs : s ≤ 32) (xs : List E)
    (hl : xs.length = 5) (hx : ∀ x ∈ xs, x ≠ zero) (low : List E)
    (qs cs : List Goldilocks) (chals : Nat → FiberFoldCoins) :
    let masked := pAdd low (shiftMonomial shiftDeg (cs.map QuinticGoldilocks.ofBase))
    let out := fun (i : Fin 5) => polynomialFoldTrace s (xs.getD i.val zero) chals masked
    projectedFibers s xs chals (vaddResidues (xs.map fun x => fiberRemainder s x low)
      (blindingResidueView s shiftDeg qs xs cs).2) =
      (⟨List.ofFn (fun i => (out i).1), List.length_ofFn⟩, (gatherByRound s).toFun (fun i => (out i).2)) := by
  intro masked out
  let high := shiftMonomial shiftDeg (cs.map QuinticGoldilocks.ofBase)
  rw [blindingResidueView.public_eqs]
  change projectedFibers s xs chals (vaddResidues _ (xs.map (fun x => fiberRemainder s x high))) = _
  rw [addRemainderRows s hs low high xs hx]
  let rows := xs.map (fun x => fiberRemainder s x masked)
  have hp (i : Fin 5) : i.val < xs.length := hl.symm ▸ i.isLt
  have hrow (i : Fin 5) : rows.getD i.val [] = fiberRemainder s (xs.getD i.val zero) masked := by
    simp only [rows,List.getD,List.getElem?_map,List.getElem?_eq_getElem (hp i),Option.map_some,Option.getD_some]
  have ht (i : Fin 5) : fiberTrace s (xs.getD i.val zero) chals
      ((fiberCoefficientList s).invFun (paddedRow (2^s) (rows.getD i.val []))) = out i := by
    let x := xs.getD i.val zero
    have hn : x ≠ zero := by
      change xs.getD i.val zero ≠ zero
      simp only [List.getD,List.getElem?_eq_getElem (hp i),Option.getD_some]
      exact hx _ (List.getElem_mem _)
    rw [hrow i]
    change fiberTrace s x chals ((fiberCoefficientList s).invFun (paddedRow (2^s) (fiberRemainder s x masked))) = _
    rw [show fiberRemainder s x masked = ((fiberCoefficientList s).toFun (polynomialFiber s x masked)).val from
        (polynomialFiber_remainder s hs x hn masked).symm, paddedRow_exact, (fiberCoefficientList s).left_inv]
    exact fiberTrace_of_polynomial s hs x hn chals masked
  unfold projectedFibers
  change ((fixedCoordinates 5).invFun (fun i => (fiberTrace s _ chals
      ((fiberCoefficientList s).invFun (paddedRow _ (rows.getD i.val [])))).1),
    (gatherByRound s).toFun (fun i => (fiberTrace s _ chals
      ((fiberCoefficientList s).invFun (paddedRow _ (rows.getD i.val [])))).2)) = _
  simp only [ht]
  rfl

#print axioms projectedFibers_masked_polynomial

private theorem fiveCoordinates_apply (s : Nat) (xs : List E) (hl : xs.length = 5)
    (hx : ∀ x ∈ xs, x ≠ zero) (cs : Nat → FiberFoldCoins) (r : FiberResidues xs (2^s)) :
    ((fiveCoordinates s xs hl hx cs).toFun r).1 = projectedFibers s xs cs r.val := by
  let row := rowsAsFunction xs hl (2^s)
  let x (i : Fin 5) := xs[i.val]'(hl.symm ▸ i.isLt)
  let t (i : Fin 5) := (fiberCoefficientList s).invFun (row.toFun r i)
  have hxpt (i : Fin 5) : xs.getD i.val zero = x i := by
    have h : i.val < xs.length := hl.symm ▸ i.isLt
    simp only [List.getD, List.getElem?_eq_getElem h, Option.getD_some, x]
  have hr (i : Fin 5) : paddedRow (2^s) (r.val.getD i.val []) = row.toFun r i := by
    have h : i.val < r.val.length := by rw [r.property.1,hl]; exact i.isLt
    simp only [List.getD, List.getElem?_eq_getElem h, Option.getD_some]
    exact paddedRow_exact (row.toFun r i)
  unfold projectedFibers
  simp only [hxpt,hr]
  change ((fixedCoordinates 5).invFun (fun i => ((fiberCoordinates s (x i) _ cs).toFun (t i)).1.1),
    (gatherByRound s).toFun (fun i => ((fiberCoordinates s (x i) _ cs).toFun (t i)).1.2)) = _
  simp only [all_fold_fiber_coordinates]
  rfl

/-- Public mask point after i successive squarings. -/
def pointAtFold : Nat → E → E
  | 0, x => x
  | i+1, x => let y := pointAtFold i x; mul y y

/-- The weights and rank checks for one round of V2.3(c). -/
structure GoodFoldRound (xs : List E) (i : Nat) where
  phi : E
  weights : FiveFoldCells
  nonzeroPhi : phi ≠ zero
  distinctPoints : (xs.map (pointAtFold i)).Nodup
  nonzeroPoints : ∀ x ∈ xs.map (pointAtFold i), x ≠ zero
  nonzeroWeights : ∀ w ∈ weights.val, w ≠ zero

noncomputable def foldWithOffset {xs : List E} {i : Nat} (hl : xs.length = 5) (r : GoodFoldRound xs i)
    (d : FiveFoldCells) : SimpleEquiv FiveFoldCells FiveFoldCells :=
  (foldScalarEquiv r.phi (xs.map (pointAtFold i)) r.weights.val r.distinctPoints
    r.nonzeroPoints r.nonzeroWeights r.nonzeroPhi ((List.length_map _).trans hl) r.weights.property).trans
    (offsetEquiv d)

theorem foldWithOffset_wire {xs : List E} {i : Nat} (hl : xs.length = 5) (r : GoodFoldRound xs i)
    (d f : FiveFoldCells) :
    ((foldWithOffset hl r d).toFun f).val =
      ZkHem.vadd d.val (foldScalars r.phi (xs.map (pointAtFold i)) r.weights.val f.val) := by
  simp only [foldWithOffset, SimpleEquiv.trans, offsetEquiv_apply, foldScalarEquiv_apply]

/-- Each successive change of coordinates may depend on all earlier even
    evaluations and wire values. This is the triangular step in V2.Z. -/
abbrev FoldHistory := List (FiveFoldCells × FiveFoldCells)

private def changeRounds : (s : Nat) → (Fin s → FoldHistory → SimpleEquiv FiveFoldCells FiveFoldCells) →
    FoldHistory → SimpleEquiv (FoldBlocks s) (FoldBlocks s)
  | 0, _, _ => SimpleEquiv.refl _
  | s+1, step, h =>
    let head := step 0 h
    equivOver head (fun f => changeRounds s (fun i => step i.succ) ((f,head.toFun f)::h))

/-- The algebraic fold wires with the actual five-scalar map in each round. -/
noncomputable def projectedFoldWires {s : Nat} {xs : List E} (hl : xs.length = 5)
    (r : (i : Fin s) → GoodFoldRound xs i.val) (d : Fin s → FoldHistory → FiveFoldCells)
    (f : FoldBlocks s) : FoldBlocks s :=
  (changeRounds s (fun i h => foldWithOffset hl (r i) (d i h)) []).toFun f

private def arrangeProjection {O A F K L : Type} :
    SimpleEquiv ((O × ((A × F) × K)) × L) ((O × A × L) × (F × K)) where
  toFun p := ((p.1.1,p.1.2.1.1,p.2),p.1.2.1.2,p.1.2.2)
  invFun t := ((t.1.1,(t.1.2.1,t.2.1),t.2.2),t.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

abbrev ProjectedBase := List Goldilocks × FiveFoldCells × LookupTriple
abbrev ProjectedPrefix (s : Nat) := ProjectedBase × FoldBlocks s

noncomputable def allFoldRealPrefix {W : Type} (s shiftDeg : Nat) (qs : List Goldilocks)
    (xs : List E) (hl : xs.length = 5) (cs : Nat → FiberFoldCoins) (rd : W → ResidueCoordinates s qs xs)
    (u : Nat → E) (k : E) (ld : W → LookupTriple) (r : (i : Fin s) → GoodFoldRound xs i.val)
    (offset : W → ProjectedBase → Fin s → FoldHistory → FiveFoldCells)
    (w : W) (coins : BlinderCoefficients s qs xs × LookupTriple) : ProjectedPrefix s :=
  let (o,rs) := maskedResidues s shiftDeg qs xs (rd w) coins.1
  let (a,f) := projectedFibers s xs cs rs
  let base := (o,a,logUpFullRankJointMaskView u k (ld w) coins.2)
  (base, projectedFoldWires hl r (offset w base) f)

abbrev ProjectedSimTape (s : Nat) (qs : List Goldilocks) (xs : List E) (hl : xs.length = 5) :=
  (FixedList Goldilocks qs.length × FiveFoldCells × LookupTriple) ×
    (FoldBlocks s × ((i : Fin 5) → FiberSlack s (xs[i.val]'(hl.symm ▸ i.isLt))))

def allFoldSimPrefix {s : Nat} {qs : List Goldilocks} {xs : List E} {hl : xs.length = 5}
    (t : ProjectedSimTape s qs xs hl) : ProjectedPrefix s :=
  ((t.1.1.val,t.1.2.1,t.1.2.2),t.2.1)

/-- The base openings, OOD evaluations, lookup triple, and every five-scalar
    fold block are independent uniform coordinates on fixed good coins. Fold
    offsets may depend on the witness and the entire preceding history. -/
theorem all_fold_projected_prefix_sim {W : Type} (s shiftDeg : Nat) (qs : List Goldilocks)
    (xs : List E) (hl : xs.length = 5) (cs : Nat → FiberFoldCoins) (rd : W → ResidueCoordinates s qs xs)
    (hqs : qs.Nodup) (hqz : ∀ q ∈ qs, q ≠ zero) (hv : MaskRootsValid s xs)
    (u : Nat → E) (k : E) (ld : W → LookupTriple) (hu : lookupLimbDet u ≠ zero)
    (hk : mul (mul k k) (mul k (u 0)) ≠ zero) (r : (i : Fin s) → GoodFoldRound xs i.val)
    (offset : W → ProjectedBase → Fin s → FoldHistory → FiveFoldCells) :
    CoinBijectionSimulated (allFoldRealPrefix s shiftDeg qs xs hl cs rd u k ld r offset)
      (@allFoldSimPrefix s qs xs hl) := by
  intro w
  obtain ⟨b,hb⟩ := v2_blinding_residue_ring_perfectly_simulated s shiftDeg qs xs hqs hqz hv (rd w)
  obtain ⟨l,hLookup⟩ := logUp_joint_rank15 u k ((lookupLimbDet_eq u) ▸ hu) hk (ld w)
  let hx := fun x (h : x ∈ xs) => (hv.omega_ne_zero h).1
  let p := fiveCoordinates s xs hl hx cs
  let prep := (equivProd (postProd b (SimpleEquiv.refl _) p) l).trans arrangeProjection
  let wires (base : FixedList Goldilocks qs.length × FiveFoldCells × LookupTriple) :=
    changeRounds s (fun i h => foldWithOffset hl (r i) (offset w (base.1.val,base.2) i h)) []
  let e := prep.trans (equivOver (SimpleEquiv.refl _) (fun base => equivProd (wires base) (SimpleEquiv.refl _)))
  refine ⟨e, fun c => ?_⟩
  have hres : maskedResidues s shiftDeg qs xs (rd w) c.1 = ((b.toFun c.1).1.val,(b.toFun c.1).2.val) := hb _
  have hlook : logUpFullRankJointMaskView u k (ld w) c.2 = l.toFun c.2 := hLookup _
  have hp : (p.toFun (b.toFun c.1).2).1 = projectedFibers s xs cs (b.toFun c.1).2.val :=
    fiveCoordinates_apply ..
  unfold allFoldRealPrefix
  rw [hres,hlook]
  dsimp only
  rw [← hp]
  simp only [allFoldSimPrefix, e, prep, equivOver, SimpleEquiv.trans, SimpleEquiv.refl, equivProd, postProd_apply, arrangeProjection]
  rfl

/-- Stage-0 algebraic transcript of one opening and the joint lookup
    disclosure. Both projected residue coordinates and every fold wire use
    the same coefficient tape. The reduced claim and opened values used by
    the mask-line verifier are functions of the public prefix. -/
theorem all_fold_projected_four_view_sim {ι κ W : Type} (s shiftDeg : Nat) (qs : List Goldilocks)
    (xs : List E) (hl : xs.length = 5) (cs : Nat → FiberFoldCoins) (rd : W → ResidueCoordinates s qs xs)
    (hqs : qs.Nodup) (hqz : ∀ q ∈ qs, q ≠ zero) (hv : MaskRootsValid s xs)
    (u : Nat → E) (k : E) (ld : W → LookupTriple) (hu : lookupLimbDet u ≠ zero)
    (hk : mul (mul k k) (mul k (u 0)) ≠ zero) (r : (i : Fin s) → GoodFoldRound xs i.val)
    (offset : W → ProjectedBase → Fin s → FoldHistory → FiveFoldCells)
    (β : E) (hβ : β ≠ zero) (ℓ : ZkHem.LinForm ι E) (opened : κ → ZkHem.LinForm ι E)
    (word : W → BlinderCoefficients s qs xs × LookupTriple → ι → E)
    (σ : ProjectedPrefix s → E) (o : ProjectedPrefix s → κ → E)
    (table : List E) (padding : Bool) (α : E) (query : W → List E)
    (sat : ∀ w v, v ∈ query w → v ∈ table) :
    let pre := allFoldRealPrefix s shiftDeg qs xs hl cs rd u k ld r offset
    (∀ w a, ℓ.app (word w a) = σ (pre w a) ∧ ∀ j, (opened j).app (word w a) = o (pre w a) j) →
    CoinBijectionSimulated
      (fun w (c : (BlinderCoefficients s qs xs × LookupTriple) × (ι → E)) =>
        let v := pre w c.1
        if denominatorProduct α (query w ++ lookupPoles table padding) = zero then none else
          some (maskLineReal β ℓ opened (word w c.1) c.2, v.2, (v.1.1,v.1.2.1), v.1.2.2))
      (fun (t : ProjectedSimTape s qs xs hl × (ι → E)) =>
        let v := allFoldSimPrefix t.1
        if α ∈ lookupPoles table padding then none else
          some (maskLineSim β ℓ opened (σ v) (o v) t.2, v.2, (v.1.1,v.1.2.1), v.1.2.2)) := by
  intro pre publicClaims w
  obtain ⟨e,he⟩ := all_fold_projected_prefix_sim s shiftDeg qs xs hl cs rd hqs hqz hv u k ld hu hk r offset w
  let line (a) : SimpleEquiv (ι → E) (ι → E) :=
    ⟨maskLine β (word w a), unmaskLine β (word w a), unmaskLine_maskLine β hβ _, maskLine_unmaskLine β hβ _⟩
  refine ⟨equivOver e line, fun c => ?_⟩
  have hp := lookup_product_retry_public table (query w) padding (sat w) α
  by_cases hit : α ∈ lookupPoles table padding
  · simp only [hit,hp.mpr hit,ite_true]
  · have hn := mt hp.mp hit
    simp only [hn,hit,ite_false]
    have hm := v2_mask_line_view_eq_sim β hβ ℓ opened (word w c.1) c.2
    obtain ⟨hσ,ho⟩ := publicClaims w c.1
    rw [hσ,funext ho] at hm
    have hpre : pre w c.1 = allFoldSimPrefix (e.toFun c.1) := he c.1
    rw [hm,hpre]
    rfl

#print axioms all_fold_projected_prefix_sim
#print axioms all_fold_projected_four_view_sim

end Qsag.ZkHemV2

namespace Qsag.ZkHemV2Cert
open ClosedWhir ClosedFs
set_option autoImplicit false
local notation "E" => QuinticGoldilocks

/-! ## Deployed domains and Merkle openings -/

private theorem stageGeometry (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) :
    ((zkHemV2ProdSched n).stages.all fun st =>
      decide (0 < st.foldK ∧ st.logDomain + st.foldK ≤ 32)) = true := by
  have h : n=16 ∨ n=17 ∨ n=18 ∨ n=19 ∨ n=20 ∨ n=21 ∨ n=22 ∨ n=23 ∨
      n=24 ∨ n=25 ∨ n=26 ∨ n=27 ∨ n=28 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [zkHemV2ProdSched.public_eqs, zkHemV2ProdStages.public_eqs] <;> decide +kernel

/-- Actual GS lists on every folded coset in every production schedule. The
    domain shift may differ by stage. The bound holds for every received word. -/
theorem deployed_stage_decode_lists (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : WhirStage) (hs : st ∈ (zkHemV2ProdSched n).stages)
    (shift : E) (hnz : shift ≠ CommRingOps.zero) (word : E → E) :
    let dom := ZkHemV2.fiberRoots st.logDomain shift
    dom.Nodup ∧ dom.length = st.domainSize ∧
      (gsDecodeList st.degBound st.agree dom word).length ≤ st.listSize := by
  have h := of_decide_eq_true (List.all_eq_true.mp (stageGeometry n lo hi) st hs)
  have hd := ZkHemV2.fiberRoots_nodup st.logDomain (by omega) hnz
  have hj := List.all_eq_true.mp (zkHemV2ProdSched_johnsonOk n lo hi) st hs
  exact ⟨hd, ZkHemV2.fiberRoots_length _ _, st.decode_list_le hj _ word hd
    (ZkHemV2.fiberRoots_length _ _)⟩

/-- Stage-0 leaf preimage. The caller fixes the tree nonce in its leaf hash. -/
structure PackedFiber (Salt : Type) (k : Nat) where
  salt : Salt
  z : Fin (2^k) → Goldilocks
  r : E

def packedStage0Table {Salt : Type} (st : WhirStage) (salt : Nat → Salt)
    (z : Nat → Goldilocks) (r : Nat → E) (j : Nat) : PackedFiber Salt st.foldK :=
  ⟨salt j, fun t => z (j + t.val * st.domainSize), r j⟩

/-- The honest authentication path at the deployed fiber index opens the
    complete strided fiber under the packed root. Works at every stage size. -/
theorem packed_stage0_root_consistent {Salt D : Type} [DecidableEq D]
    (st : WhirStage) (M : MerkleSetup D (PackedFiber Salt st.foldK))
    (salt : Nat → Salt) (z : Nat → Goldilocks) (r : Nat → E) (j : Nat) (hj : j < st.domainSize) :
    let t := packedStage0Table st salt z r
    let p := treePathFrom M.node (M.oracleLeaves 0 t) 0 j st.logDomain
    openingOk M (fun _ => st.logDomain) (fun _ => M.root 0 st.logDomain t) (0,j) (t j,p) = true ∧
      (∀ a, (t j).z a = z (j + a.val * st.domainSize)) := by
  dsimp only
  constructor
  · rw [openingOk.public_eqs]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hj, decide_eq_true (treePathFrom_length ..)⟩,
      decide_eq_true ?_⟩
    have h := treePathFrom_opens M.node (M.oracleLeaves 0 (packedStage0Table st salt z r)) st.logDomain 0 j
    rw [Nat.zero_add, Nat.div_eq_of_lt (show j < 2^st.logDomain from hj)] at h
    simpa only [MerkleSetup.root.public_eqs, treeNode.public_eq_1, MerkleSetup.oracleLeaves.public_eqs] using h
  · intro a; rfl

/-- Packed fiber paths and the scalar-leaf paths required by the current
    succinct verifier have different lengths for every deployed stage. -/
theorem deployed_scalar_verifier_rejects_packed_path {D : Type} [DecidableEq D]
    (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) (env : WhirEnv E) (i : Nat) (st : WhirStage)
    (hst : (zkHemV2ProdSched n).stages[i]? = some st) (M : MerkleSetup D E)
    (roots : Nat → D) (j : Nat) (v : E) (path : List D) (hlen : path.length = st.logDomain) :
    openingOk M (whirOracleIop env (zkHemV2ProdSched n) 400).depth roots (i,j) (v,path) = false := by
  have hs := List.mem_of_getElem? hst
  have h := of_decide_eq_true (List.all_eq_true.mp (stageGeometry n lo hi) st hs)
  have hn : path.length ≠ st.logDomain + st.foldK := by omega
  simp only [openingOk.public_eqs, whirOracleIop, stageDepth.public_eqs, hst, hn, decide_false, Bool.and_false,
    Bool.false_and]

/-- Resolve a root against the forest of tables actually committed at this
    oracle. A collision can select a different table with the same root. -/
def registeredTable {D F : Type} [DecidableEq D] (M : MerkleSetup D F)
    (depth : Nat → Nat) (forest : Nat → List (Nat → F)) (fallback : Nat → F)
    (i : Nat) (root : D) : Nat → F :=
  ((forest i).find? (fun t => decide (M.root i (depth i) t = root))).getD fallback

theorem registeredTable_root {D F : Type} [DecidableEq D] (M : MerkleSetup D F)
    (depth : Nat → Nat) (forest : Nat → List (Nat → F)) (fallback : Nat → F)
    (i : Nat) (t : Nat → F) (ht : t ∈ forest i) :
    M.root i (depth i) (registeredTable M depth forest fallback i (M.root i (depth i) t)) =
      M.root i (depth i) t := by
  let good (u : Nat → F) := decide (M.root i (depth i) u = M.root i (depth i) t)
  change M.root i (depth i) (((forest i).find? good).getD fallback) = M.root i (depth i) t
  cases he : (forest i).find? good with
  | none =>
    have h := List.find?_eq_none.mp he t ht
    simp [good] at h
  | some u =>
    have h : good u = true := List.find?_some he
    exact of_decide_eq_true h

/-- Encode the tables of a strategy at precisely the commit rounds consumed
    by the succinct WHIR bridge. Values of other public fields are arbitrary. -/
def tableBackedMessages {D : Type} (sched : WhirVerifierSchedule) (M : MerkleSetup D E)
    (tables : Nat → Nat → E) (pub : Nat → WhirPub E) : List (SuccinctRoundMsg D (WhirPub E)) :=
  (List.range sched.numRounds).map fun r =>
    ⟨(stageOfCommitRound sched.stages r).map (fun j =>
      M.root (j+1) (stageDepth sched.stages (j+1)) (tables (j+1))), pub r⟩

private theorem tableBackedRoots {D : Type} (sched : WhirVerifierSchedule) (M : MerkleSetup D E)
    (dflt : D) (tables : Nat → Nat → E) (pub : Nat → WhirPub E) (i : Nat) (hi : i < sched.stages.length) :
    whirSuccinctRootsOf sched.stages dflt (fun _ => M.root 0 (stageDepth sched.stages 0) (tables 0))
      (tableBackedMessages sched M tables pub) i = M.root i (stageDepth sched.stages i) (tables i) := by
  cases i with
  | zero => rw [whirSuccinctRootsOf.public_eq_1]
  | succ j =>
    have hj : j < sched.stages.length := by omega
    have hr : commitRoundIdx sched.stages j < (List.range sched.numRounds).length := by
      rw [List.length_range]; exact commitRoundIdx_lt_roundsOf _ _ hj
    simp only [whirSuccinctRootsOf.public_eqs, tableBackedMessages, List.getElem?_map, List.getElem?_eq_getElem hr,
      Option.map_some, List.getElem_range, stageOfCommitRound_commitRoundIdx _ _ hj, Option.getD_some]

/-- For root-producing decoders, this supplies the exact queried-root
    equality used by deployed soundness. The table selector is constructed
    once over the finite strategy and does not depend on the random oracle. -/
theorem deployed_table_backed_fs_roots {D : Type} [DecidableEq D] {cardX : Nat}
    (n : Nat) (env : WhirEnv E) (M : MerkleSetup D E) (dflt : D)
    (codec : FsCodec (SuccinctRoundMsg D (WhirPub E)) (zkHemV2ProdSched n).numRounds cardX)
    (statementTable : Nat → E) (committed : Fin cardX → Nat → Nat → E)
    (pub : Fin cardX → Nat → WhirPub E)
    (claim : E) (H : Fin cardX → BitVec 400) (o : Fin cardX)
    (produces : codec.dec o = tableBackedMessages (zkHemV2ProdSched n) M
      (fun i => if i = 0 then statementTable else committed o i) (pub o)) :
    let sc := zkHemV2ProdSched n
    let depth := stageDepth sc.stages
    let B := whirSuccinctBridge env sc 400 dflt
    let init := fun _ : Nat => M.root 0 (depth 0) statementTable
    let str := fsTranscript codec H (codec.dec o)
    let forest := fun i => statementTable :: List.ofFn (fun a => committed a i)
    let tbl := registeredTable M depth forest statementTable
    ∀ q ∈ (whirOracleIop env sc 400).queries claim (str.map (fun v => (v.1.pub,v.2))),
      M.root q.1 (depth q.1) (tbl q.1 (B.rootsOf init (str.map Prod.fst) q.1)) =
        B.rootsOf init (str.map Prod.fst) q.1 := by
  intro sc depth B init str forest tbl q hq
  have hs : q.1 < sc.stages.length := by
    change q ∈ whirQueries env sc _ at hq
    rw [whirQueries.public_eqs] at hq
    cases he : splitStages sc.stages (str.map fun v => (v.1.pub, v.2)) with
    | none => rw [he] at hq; cases hq
    | some vs =>
      rw [he] at hq
      exact Nat.zero_add sc.stages.length ▸ allStageQueries_fst_lt env sc.stages vs 0 q hq
  let t := fun i => if i = 0 then statementTable else committed o i
  have hwire : str.map Prod.fst = tableBackedMessages sc M t (pub o) :=
    by simpa only [str, fsTranscript.public_eqs] using (fsAux_map_fst codec H (codec.dec o) []).trans produces
  have hroot : B.rootsOf init (str.map Prod.fst) q.1 = M.root q.1 (depth q.1) (t q.1) := by
    rw [hwire]; simp only [B, whirSuccinctBridge_rootsOf]; exact tableBackedRoots sc M dflt t (pub o) q.1 hs
  rw [hroot]
  apply registeredTable_root
  if hz : q.1 = 0 then
    simp only [t,hz,ite_true]; exact List.mem_cons_self
  else
    simp only [t,hz,ite_false]
    exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨o,rfl⟩)

/-! ## Out-of-domain rounds on a finite challenge space -/

set_option exponentiation.threshold 512

private theorem first_ood_getD (k : Nat) (f o t : RatBound) (rest : List RatBound) :
    ((List.replicate k f ++ [o,t]) ++ rest).getD k RatBound.one = o := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ, List.cons_append, List.getD_cons_succ] using ih

theorem deployed_first_ood_data (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) :
    let sc := zkHemV2ProdSched n
    let r := commitRoundIdx sc.stages 0
    let b := sc.roundBounds.getD r RatBound.one
    r < sc.numRounds ∧ b.num * 2^400 < b.den ∧
      ((sc.stages.head?).map fun st => decide (st.oodCount = 5 ∧ 5 ≤ st.degBound)) = some true := by
  let good (st : WhirStage) := decide (st.oodCount = 5 ∧ 5 ≤ st.degBound ∧
    st.listSize * (st.listSize - 1) / 2 * st.degBound^st.oodCount * 2^400 <
      quinticGoldilocksCard^st.oodCount)
  have hg : ((zkHemV2ProdStages n).head?).map good = some true := by
    have h : n=16 ∨ n=17 ∨ n=18 ∨ n=19 ∨ n=20 ∨ n=21 ∨ n=22 ∨ n=23 ∨
        n=24 ∨ n=25 ∨ n=26 ∨ n=27 ∨ n=28 := by omega
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [zkHemV2ProdStages.public_eqs] <;> decide +kernel
  simp only [zkHemV2ProdSched.public_eqs, WhirVerifierSchedule.roundBounds_eq, WhirVerifierSchedule.numRounds]
  cases he : zkHemV2ProdStages n with
  | nil => simp [he] at hg
  | cons st rest =>
    have ht : good st = true := Option.some.inj (by simpa only [he, List.head?_cons, Option.map_some] using hg)
    obtain ⟨hc,hd,hs⟩ := of_decide_eq_true ht
    have hl := commitRoundIdx_lt_roundsOf (st :: rest) 0 (by simp)
    refine ⟨hl, ?_, by simp only [List.head?_cons, Option.map_some, hc, hd, decide_true, and_self]⟩
    rw [commitRoundIdx.public_eq_2, stagesRoundBounds_cons, WhirStage.roundBounds_eq, first_ood_getD, WhirStage.oodBound_eq]
    simpa only [binom2_eq] using hs

/-- The first five-point OOD round has less probability budget than a single
    seed. Every certificate for the production schedule must give it zero flips. -/
theorem deployed_cert_first_ood_zero (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (env : WhirEnv E) (cert : WhirScheduleCert env (zkHemV2ProdSched n) 400) :
    cert.cert.bad ⟨commitRoundIdx (zkHemV2ProdSched n).stages 0,
      (deployed_first_ood_data n lo hi).1⟩ = 0 := by
  let sc := zkHemV2ProdSched n
  let r : Fin sc.numRounds := ⟨commitRoundIdx sc.stages 0, (deployed_first_ood_data n lo hi).1⟩
  let b := sc.roundBounds.getD r.val RatBound.one
  change cert.cert.bad r = 0
  have cov : cert.cert.bad r * b.den ≤ b.num * 2^400 := cert.covers r
  have small : b.num * 2^400 < b.den := (deployed_first_ood_data n lo hi).2.1
  cases hv : cert.cert.bad r with
  | zero => rfl
  | succ k =>
    have h := Nat.mul_le_mul_right b.den (show 1 ≤ cert.cert.bad r by omega)
    rw [Nat.one_mul] at h
    omega

/-- A fixed monic degree-five polynomial that collides with the zero
    polynomial on every OOD point of at least one 400-bit seed. The polynomial
    is fixed before the seed in the finite count is varied. -/
theorem five_ood_seed_collision (env : WhirEnv E) (seed : Fin (2^400)) :
    ∃ P : List E, P.length = 6 ∧ P.getD 5 CommRingOps.zero = CommRingOps.one ∧
      1 ≤ qsum (2^400) (fun i => if (List.finRange 5).all (fun j =>
        decide (RoundPoly.evalCoeffs P (env.chalField i.val j.val) = CommRingOps.zero)) then 1 else 0) := by
  let pts := List.ofFn (fun j : Fin 5 => env.chalField seed.val j.val)
  refine ⟨vanishingPoly pts, by simp [vanishingPoly_length, pts], ?_, ?_⟩
  · simpa [pts] using vanishingPoly_last_one pts
  · calc
      1 = qsum (2^400) (fun i => if i = seed then 1 else 0) := (qsum_eq_indicator _ _).symm
      _ ≤ _ := by
        apply qsum_le_qsum
        intro i
        by_cases hi : i = seed
        · subst i
          have hit : (List.finRange 5).all (fun j => decide (RoundPoly.evalCoeffs (vanishingPoly pts)
              (env.chalField seed.val j.val) = CommRingOps.zero)) = true := by
            apply List.all_eq_true.mpr
            intro j _
            exact decide_eq_true (eval_vanishingPoly_eq_zero_of_mem (List.mem_ofFn.mpr ⟨j,rfl⟩))
          simp only [hit, ite_true, Nat.le_refl]
        · simp [hi]

/-- Arithmetic for a one-point alternative. If the first OOD field element
    has at most this many seed preimages, the pairwise root-count envelope
    remains below 2^-277 at every deployed stage. -/
theorem deployed_single_ood_budget (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) :
    ((zkHemV2ProdSched n).stages.all fun st =>
      decide ((2^400 / quinticGoldilocksCard + 1) *
        (st.listSize * (st.listSize - 1) / 2) * st.degBound * 2^277 < 2^400)) = true := by
  have h : n=16 ∨ n=17 ∨ n=18 ∨ n=19 ∨ n=20 ∨ n=21 ∨ n=22 ∨ n=23 ∨
      n=24 ∨ n=25 ∨ n=26 ∨ n=27 ∨ n=28 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [zkHemV2ProdSched.public_eqs, zkHemV2ProdStages.public_eqs] <;> decide +kernel

/-- The two polynomials can occur in the *same* actual GS list. The shared
    part of the two agreement sets has size max(0,2A-n), leaving room for
    every prescribed OOD point in a monic polynomial of bounded degree. -/
private theorem colliding_decode_pair (dom pts : List E) (nd : dom.Nodup) (d A : Nat)
    (hA : A ≤ dom.length) (hdA : d+1 ≤ A) (hd : (2*A-dom.length) + pts.length ≤ d) :
    ∃ word : E → E, ∃ P ∈ gsDecodeList d A dom word, ∃ Q ∈ gsDecodeList d A dom word,
      P ≠ Q ∧ ∀ x ∈ pts, RoundPoly.evalCoeffs P.coeffs x = RoundPoly.evalCoeffs Q.coeffs x := by
  let left := dom.take A
  let right := dom.drop A
  let k := 2*A - dom.length
  let common := left.take k
  have cut : left ++ right = dom := List.take_append_drop A dom
  have nl : left.length = A := by simp [left,Nat.min_eq_left hA]
  have nr : right.length = dom.length - A := List.length_drop
  have hk : k ≤ left.length := by dsimp only [k]; omega
  have nc : common.length = k := by simp [common,Nat.min_eq_left hk]
  let roots := common ++ pts
  let P : GsUniPoly E := GsUniPoly.ofCoeffs (vanishingPoly roots)
  let Q : GsUniPoly E := GsUniPoly.ofCoeffs []
  let val := fun x => RoundPoly.evalCoeffs P.coeffs x
  have evalP x : val x = RoundPoly.evalCoeffs (vanishingPoly roots) x :=
    evalCoeffs_trimPoly x _
  have van x (hx : x ∈ roots) : val x = CommRingOps.zero :=
    (evalP x).trans (eval_vanishingPoly_eq_zero_of_mem hx)
  have diff : P ≠ Q := by
    intro eq
    have h := congrArg (fun t : GsUniPoly E => coeffAt t.coeffs roots.length) eq
    change coeffAt (trimPoly (vanishingPoly roots)) roots.length = CommRingOps.zero at h
    rw [coeffAt_trimPoly] at h
    exact LawfulField.one_ne_zero ((vanishingPoly_last_one roots).symm.trans h)
  let word := fun x => if x ∈ left then CommRingOps.zero else val x
  let okP := fun x => decide (RoundPoly.evalCoeffs P.coeffs x = word x)
  let okQ := fun x => decide (RoundPoly.evalCoeffs Q.coeffs x = word x)
  have eqQ : left.filter okQ = left := by
    apply List.filter_eq_self.mpr
    intro x hx
    change decide (CommRingOps.zero = word x) = true
    simp only [word,hx,ite_true,decide_true]
  have eqRight : right.filter okP = right := by
    rw [← cut,List.nodup_append] at nd
    apply List.filter_eq_self.mpr
    intro x hx
    have hn : x ∉ left := fun hl => nd.2.2 x hl x hx rfl
    change decide (val x = word x) = true
    simp only [word,hn,ite_false,decide_true]
  have eqCommon : common.filter okP = common := by
    apply List.filter_eq_self.mpr
    intro x hx
    have hxl : x ∈ left := List.mem_of_mem_take hx
    have hz := van x (List.mem_append_left pts hx)
    change decide (val x = word x) = true
    simp only [word,hxl,ite_true,hz,decide_true]
  have lc : k ≤ (left.filter okP).length := by
    have split : common ++ left.drop k = left := List.take_append_drop k left
    calc
      k = (common.filter okP).length := by rw [eqCommon,nc]
      _ ≤ ((common ++ left.drop k).filter okP).length := by simp only [List.filter_append,List.length_append]; omega
      _ = _ := congrArg (fun l => (l.filter okP).length) split
  refine ⟨word,P,(mem_gsDecodeList_iff word nd hdA P).mpr ⟨?_,?_⟩,
    Q,(mem_gsDecodeList_iff word nd hdA Q).mpr ⟨by change 0 ≤ _; exact Nat.zero_le _, ?_⟩,diff,?_⟩
  · apply Nat.le_trans (trimPoly_length_le (vanishingPoly roots))
    simp only [vanishingPoly_length,roots,List.length_append,nc]; omega
  · change A ≤ (dom.filter okP).length
    rw [← cut,List.filter_append,List.length_append,eqRight,nr]
    dsimp only [k] at lc; omega
  · change A ≤ (dom.filter okQ).length
    rw [← cut,List.filter_append,List.length_append,eqQ,nl]; omega
  · intro x hx
    exact van x (List.mem_append_right common hx)

/-- For every production Stage-0 coset and every fixed commit-challenge seed
    there is a received word with two distinct GS candidates agreeing on the
    five points generated by that seed. -/
theorem deployed_first_ood_list_collision (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : WhirStage) (first : (zkHemV2ProdSched n).stages.head? = some st)
    (shift : E) (nz : shift ≠ CommRingOps.zero) (env : WhirEnv E) (seed : Fin (2^400)) :
    let dom := ZkHemV2.fiberRoots st.logDomain shift
    ∃ word : E → E, ∃ P ∈ gsDecodeList st.degBound st.agree dom word,
      ∃ Q ∈ gsDecodeList st.degBound st.agree dom word, P ≠ Q ∧
        ∀ j : Fin 5, RoundPoly.evalCoeffs P.coeffs (env.chalField seed.val j.val) =
          RoundPoly.evalCoeffs Q.coeffs (env.chalField seed.val j.val) := by
  let good (t : WhirStage) := decide (t.logDomain ≤ 32 ∧ t.agree ≤ t.domainSize ∧
    t.degBound+1 ≤ t.agree ∧ (2*t.agree-t.domainSize)+5 ≤ t.degBound)
  have hg : ((zkHemV2ProdSched n).stages.head?).map good = some true := by
    have h : n=16 ∨ n=17 ∨ n=18 ∨ n=19 ∨ n=20 ∨ n=21 ∨ n=22 ∨ n=23 ∨
        n=24 ∨ n=25 ∨ n=26 ∨ n=27 ∨ n=28 := by omega
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [zkHemV2ProdSched.public_eqs, zkHemV2ProdStages.public_eqs] <;> decide +kernel
  rw [first] at hg
  obtain ⟨hs,ha,hd,hroom⟩ := of_decide_eq_true (show good st = true from Option.some.inj hg)
  let dom := ZkHemV2.fiberRoots st.logDomain shift
  let pts := List.ofFn (fun j : Fin 5 => env.chalField seed.val j.val)
  have len : dom.length = st.domainSize := ZkHemV2.fiberRoots_length ..
  obtain ⟨w,P,hP,Q,hQ,ne,hit⟩ := colliding_decode_pair dom pts (ZkHemV2.fiberRoots_nodup _ hs nz)
    st.degBound st.agree (len.symm ▸ ha) hd (by rw [len]; simpa only [pts,List.length_ofFn] using hroom)
  exact ⟨w,P,hP,Q,hQ,ne,fun j => hit _ (List.mem_ofFn.mpr ⟨j,rfl⟩)⟩


/-- Counting all pairs in the decoded list that coincide on the five
    deterministically expanded points cannot discharge Stage 0's OOD bound,
    even for a particular coset and a fixed challenge decoder. -/
theorem deployed_ood_pair_count_exceeds_bound (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : WhirStage) (first : (zkHemV2ProdSched n).stages.head? = some st)
    (shift : E) (nz : shift ≠ CommRingOps.zero) (env : WhirEnv E) :
    let sc := zkHemV2ProdSched n
    let bound := sc.roundBounds.getD (commitRoundIdx sc.stages 0) RatBound.one
    let dom := ZkHemV2.fiberRoots st.logDomain shift
    ∃ word : E → E, ∃ P ∈ gsDecodeList st.degBound st.agree dom word,
      ∃ Q ∈ gsDecodeList st.degBound st.agree dom word, P ≠ Q ∧
        ¬ RatBound.le ⟨qsum (2^400) (fun i => if (List.finRange 5).all (fun j =>
          decide (RoundPoly.evalCoeffs P.coeffs (env.chalField i.val j.val) =
            RoundPoly.evalCoeffs Q.coeffs (env.chalField i.val j.val))) then 1 else 0),
          2^400, Nat.two_pow_pos 400⟩ bound := by
  intro sc bound dom
  let a : Fin (2^400) := ⟨0,Nat.two_pow_pos _⟩
  obtain ⟨w,P,hP,Q,hQ,ne,ha⟩ := deployed_first_ood_list_collision n lo hi st first shift nz env a
  refine ⟨w,P,hP,Q,hQ,ne,?_⟩
  let hit (i : Fin (2^400)) := (List.finRange 5).all fun j =>
    decide (RoundPoly.evalCoeffs P.coeffs (env.chalField i.val j.val) =
      RoundPoly.evalCoeffs Q.coeffs (env.chalField i.val j.val))
  have yes : hit a = true := List.all_eq_true.mpr (fun j _ => decide_eq_true (ha j))
  have count : 1 ≤ qsum (2^400) (fun i => if hit i then 1 else 0) := by
    calc
      1 = qsum (2^400) (fun i => if i = a then 1 else 0) := (qsum_eq_indicator _ _).symm
      _ ≤ _ := by
        apply qsum_le_qsum
        intro i
        by_cases eq : i = a
        · subst i; simp only [yes,ite_true,Nat.le_refl]
        · simp [eq]
  intro h
  have cov : qsum (2^400) (fun i => if hit i then 1 else 0) * bound.den ≤ bound.num * 2^400 := h
  have low := Nat.mul_le_mul_right bound.den count
  rw [Nat.one_mul] at low
  exact Nat.not_le_of_lt (deployed_first_ood_data n lo hi).2.1 (Nat.le_trans low cov)

#print axioms deployed_ood_pair_count_exceeds_bound

#print axioms deployed_first_ood_list_collision

#print axioms deployed_cert_first_ood_zero
#print axioms five_ood_seed_collision
#print axioms deployed_single_ood_budget

#print axioms deployed_table_backed_fs_roots

#print axioms deployed_stage_decode_lists
#print axioms packed_stage0_root_consistent
#print axioms deployed_scalar_verifier_rejects_packed_path
#print axioms registeredTable_root
end Qsag.ZkHemV2Cert

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


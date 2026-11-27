module

public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.BlindVcSponge
import Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [-instance] Fin.instLinearOrderPackage

set_option autoImplicit false

/-! ### §4.3 `Vec`, `SimpleEquiv` Combinators, PRG Coin Tapes & 3-Party `absorbRate6Sponge3` + 6-Limb Merkle ZKBoo Verifier -/

/-- Length-indexed constructive vector (`0` Mathlib dependencies, explicit `DecidableEq`). -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

def Vec.head {α : Type} {n : Nat} : Vec α (n + 1) → α
  | .cons x _ => x

def Vec.tail {α : Type} {n : Nat} : Vec α (n + 1) → Vec α n
  | .cons _ xs => xs

private theorem Vec.eta_cons {α : Type} {n : Nat} (v : Vec α (n + 1)) :
    Vec.cons v.head v.tail = v := by
  cases v; rfl

@[expose] def Vec.toList {α : Type} : {n : Nat} → Vec α n → List α
  | 0, .nil => []
  | _ + 1, .cons x xs => x :: xs.toList

theorem Vec.toList_length {α : Type} : ∀ {n : Nat} (v : Vec α n), v.toList.length = n
  | 0, .nil => rfl
  | _ + 1, .cons _ xs => by simp [Vec.toList, Vec.toList_length xs]

theorem Vec.toList_injective {α : Type} : ∀ {n : Nat} {u v : Vec α n},
    u.toList = v.toList → u = v
  | 0, .nil, .nil, _ => rfl
  | _ + 1, .cons x xs, .cons y ys, h => by
    simp only [Vec.toList] at h
    injection h with hx hxs
    rw [hx, Vec.toList_injective hxs]

def Vec.ofList {α : Type} : (xs : List α) → Vec α xs.length
  | [] => .nil
  | x :: xs => .cons x (Vec.ofList xs)

theorem Vec.toList_ofList {α : Type} : ∀ (xs : List α), (Vec.ofList xs).toList = xs
  | [] => rfl
  | x :: xs => by simp [Vec.ofList, Vec.toList, Vec.toList_ofList xs]

@[expose] def Vec.replicate {α : Type} : (n : Nat) → α → Vec α n
  | 0, _ => .nil
  | n + 1, x => .cons x (Vec.replicate n x)

private theorem Vec.cons_inj {α : Type} {n : Nat} {x y : α} {xs ys : Vec α n}
    (h : Vec.cons x xs = Vec.cons y ys) : x = y ∧ xs = ys := by
  cases h
  exact ⟨rfl, rfl⟩

def Vec.decEq {α : Type} [DecidableEq α] : {n : Nat} → (u v : Vec α n) → Decidable (u = v)
  | 0, .nil, .nil => isTrue rfl
  | _ + 1, .cons x xs, .cons y ys =>
    match _root_.decEq x y, Vec.decEq xs ys with
    | isTrue hx, isTrue hxs => isTrue (by subst hx hxs; rfl)
    | isFalse hx, _ => isFalse (fun h => hx (Vec.cons_inj h).1)
    | _, isFalse hxs => isFalse (fun h => hxs (Vec.cons_inj h).2)

instance {α : Type} [DecidableEq α] {n : Nat} : DecidableEq (Vec α n) := Vec.decEq

/-- Dependent `Vec` cons bijection (`0 Classical.choice`) for multi-round / multi-level simulation. -/
@[expose] def seDepConsToFun {α β : Type} {n : Nat}
    (eqHead : SimpleEquiv α β)
    (eqTail : α → SimpleEquiv (Vec α n) (Vec β n)) :
    Vec α (n + 1) → Vec β (n + 1)
  | .cons x xs => .cons (eqHead.toFun x) ((eqTail x).toFun xs)

def seDepConsInvFun {α β : Type} {n : Nat}
    (eqHead : SimpleEquiv α β)
    (eqTail : α → SimpleEquiv (Vec α n) (Vec β n)) :
    Vec β (n + 1) → Vec α (n + 1)
  | .cons y ys =>
    let x := eqHead.invFun y
    .cons x ((eqTail x).invFun ys)

@[expose] def seDepCons {α β : Type} {n : Nat}
    (eqHead : SimpleEquiv α β)
    (eqTail : α → SimpleEquiv (Vec α n) (Vec β n)) :
    SimpleEquiv (Vec α (n + 1)) (Vec β (n + 1)) where
  toFun := seDepConsToFun eqHead eqTail
  invFun := seDepConsInvFun eqHead eqTail
  left_inv
    | .cons x xs => by
      simp only [seDepConsToFun, seDepConsInvFun]
      rw [eqHead.left_inv x, (eqTail x).left_inv xs]
  right_inv
    | .cons y ys => by
      simp only [seDepConsToFun, seDepConsInvFun]
      rw [eqHead.right_inv y, (eqTail (eqHead.invFun y)).right_inv ys]

private def seVecCongr {α β : Type} : {n : Nat} → (Fin n → SimpleEquiv α β) → SimpleEquiv (Vec α n) (Vec β n)
  | 0, _ =>
    { toFun := fun _ => .nil
      invFun := fun _ => .nil
      left_inv := fun | .nil => rfl
      right_inv := fun | .nil => rfl }
  | n + 1, fs =>
    seDepCons (fs ⟨0, Nat.zero_lt_succ n⟩)
      (fun _ => seVecCongr (fun i => fs ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))

abbrev VcWire3 := Fin 3 → Goldilocks
abbrev VcLane4_3 := Fin 3 → Lane4
abbrev VcLane6_3 := Fin 3 → Lane6
abbrev VcState12_3 := Fin 3 → Poseidon2State12

/-- Cyclic adjacent ZKBoo party `(e + 1) % 3` (`blind_vc.rs:334, 1916`). -/
@[expose] def vcNextParty3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

/-- Unopened 3rd ZKBoo party `(e + 2) % 3` (`blind_vc.rs:766`). -/
@[expose] def vcUnopenedParty3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1

/-- Assemble a 3-party assignment from values at `(e, (e+1)%3, (e+2)%3)`. -/
@[expose] def mkParty3At {α : Type} (e : Fin 3) (vE vE1 vU : α) : Fin 3 → α :=
  match e with
  | ⟨0, _⟩ => fun | ⟨0, _⟩ => vE | ⟨1, _⟩ => vE1 | ⟨2, _⟩ => vU
  | ⟨1, _⟩ => fun | ⟨0, _⟩ => vU | ⟨1, _⟩ => vE  | ⟨2, _⟩ => vE1
  | ⟨2, _⟩ => fun | ⟨0, _⟩ => vE1 | ⟨1, _⟩ => vU | ⟨2, _⟩ => vE

theorem fin3_eq_012 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨iv, hiv⟩
  have hc : iv = 0 ∨ iv = 1 ∨ iv = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem BlindVc.fin3_all {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  rcases fin3_eq_012 i with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

theorem mkParty3At_e {α : Type} (e : Fin 3) (vE vE1 vU : α) :
    mkParty3At e vE vE1 vU e = vE := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

theorem mkParty3At_next {α : Type} (e : Fin 3) (vE vE1 vU : α) :
    mkParty3At e vE vE1 vU (vcNextParty3 e) = vE1 := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

theorem mkParty3At_unopened {α : Type} (e : Fin 3) (vE vE1 vU : α) :
    mkParty3At e vE vE1 vU (vcUnopenedParty3 e) = vU := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

theorem mkParty3At_eta {α : Type} (e : Fin 3) (f : Fin 3 → α) :
    mkParty3At e (f e) (f (vcNextParty3 e)) (f (vcUnopenedParty3 e)) = f := by
  funext i
  rcases fin3_eq_012 e with rfl | rfl | rfl <;>
    rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl

theorem vcNextParty3_next_eq_unopened (e : Fin 3) :
    vcNextParty3 (vcNextParty3 e) = vcUnopenedParty3 e := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

@[expose] def vcSum3 (w : VcWire3) : Goldilocks :=
  Goldilocks.add (Goldilocks.add (w 0) (w 1)) (w 2)

def vcSumLane4_3 (w : VcLane4_3) : Lane4 :=
  lane4Add (lane4Add (w 0) (w 1)) (w 2)

def vcSumLane6_3 (w : VcLane6_3) : Lane6 :=
  lane6Add (lane6Add (w 0) (w 1)) (w 2)

def vcSumState12_3 (st : VcState12_3) : Poseidon2State12 :=
  state12Add (state12Add (st 0) (st 1)) (st 2)

theorem vcSumLane4_3_eq (w : VcLane4_3) :
    vcSumLane4_3 w =
      ⟨vcSum3 (fun i => (w i).x0), vcSum3 (fun i => (w i).x1),
       vcSum3 (fun i => (w i).x2), vcSum3 (fun i => (w i).x3)⟩ := by
  unfold vcSumLane4_3 vcSum3
  simp only [lane4Add_eq]

theorem vcSumLane6_3_eq (w : VcLane6_3) :
    vcSumLane6_3 w =
      ⟨vcSum3 (fun i => (w i).x0), vcSum3 (fun i => (w i).x1),
       vcSum3 (fun i => (w i).x2), vcSum3 (fun i => (w i).x3),
       vcSum3 (fun i => (w i).x4), vcSum3 (fun i => (w i).x5)⟩ := by rfl

private theorem vcSumState12_3_lanes (st : VcState12_3) :
    vcSumState12_3 st =
      ⟨vcSumLane4_3 (fun i => (st i).b0),
       vcSumLane4_3 (fun i => (st i).b1),
       vcSumLane4_3 (fun i => (st i).b2)⟩ := by
  unfold vcSumState12_3 vcSumLane4_3
  simp only [state12Add_eq, lane4Add_eq]

private theorem vcSumState12_3_of6 (r c : VcLane6_3) :
    vcSumState12_3 (fun i => mkState12Of6 (r i) (c i)) =
      mkState12Of6 (vcSumLane6_3 r) (vcSumLane6_3 c) := by
  rw [vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, mkState12Of6.public_eqs, vcSumLane6_3_eq]

private theorem state12Rate6_vcSum (st : VcState12_3) :
    state12Rate6 (vcSumState12_3 st) = vcSumLane6_3 (fun i => state12Rate6 (st i)) := by
  rw [vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, state12Rate6.public_eqs, vcSumLane6_3_eq]

private theorem state12Cap6_vcSum (st : VcState12_3) :
    state12Cap6 (vcSumState12_3 st) = vcSumLane6_3 (fun i => state12Cap6 (st i)) := by
  rw [vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, state12Cap6.public_eqs, vcSumLane6_3_eq]

theorem vcSum3_zero : vcSum3 (fun _ => Goldilocks.zero) = Goldilocks.zero := by
  unfold vcSum3
  rw [← goldOfInt_nat Goldilocks.zero]
  simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1

private theorem vcSumLane6_3_zero : vcSumLane6_3 (fun _ => lane6Zero) = lane6Zero := by
  rw [vcSumLane6_3_eq]
  simp only [lane6Zero.public_eqs, vcSum3_zero]

private theorem vcSum3_add (a b : VcWire3) :
    vcSum3 (fun i => Goldilocks.add (a i) (b i)) = Goldilocks.add (vcSum3 a) (vcSum3 b) := by
  unfold vcSum3
  dsimp only
  rw [← goldOfInt_nat (a 0), ← goldOfInt_nat (b 0), ← goldOfInt_nat (a 1),
      ← goldOfInt_nat (b 1), ← goldOfInt_nat (a 2), ← goldOfInt_nat (b 2)]
  simp only [goldOfInt_add]; congr 1; omega

private theorem vcSum3_sub (a b : VcWire3) :
    vcSum3 (fun i => Goldilocks.sub (a i) (b i)) = Goldilocks.sub (vcSum3 a) (vcSum3 b) := by
  unfold vcSum3
  dsimp only
  rw [← goldOfInt_nat (a 0), ← goldOfInt_nat (b 0), ← goldOfInt_nat (a 1),
      ← goldOfInt_nat (b 1), ← goldOfInt_nat (a 2), ← goldOfInt_nat (b 2)]
  simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega

private theorem vcSumLane6_3_add (a b : VcLane6_3) :
    vcSumLane6_3 (fun i => lane6Add (a i) (b i)) = lane6Add (vcSumLane6_3 a) (vcSumLane6_3 b) := by
  simp only [vcSumLane6_3_eq, lane6Add, vcSum3_add]

theorem vcUnopened_of_sum3 (e : Fin 3) {w : VcWire3} {target : Goldilocks}
    (hSum : vcSum3 w = target) :
    w = mkParty3At e (w e) (w (vcNextParty3 e))
          (Goldilocks.sub (Goldilocks.sub target (w e)) (w (vcNextParty3 e))) := by
  rw [← hSum]
  have hUn : w (vcUnopenedParty3 e) =
      Goldilocks.sub (Goldilocks.sub (vcSum3 w) (w e)) (w (vcNextParty3 e)) := by
    unfold vcSum3
    rcases fin3_eq_012 e with rfl | rfl | rfl <;>
      (dsimp only [vcNextParty3, vcUnopenedParty3];
       rw [← goldOfInt_nat (w 0), ← goldOfInt_nat (w 1), ← goldOfInt_nat (w 2)];
       simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega)
  rw [← hUn, mkParty3At_eta]

theorem vcUnopened_of_sumLane6_3 (e : Fin 3) {w : VcLane6_3} {target : Lane6}
    (hSum : vcSumLane6_3 w = target) :
    w = mkParty3At e (w e) (w (vcNextParty3 e))
          (lane6Sub (lane6Sub target (w e)) (w (vcNextParty3 e))) := by
  have hx0 := vcUnopened_of_sum3 e (w := fun i => (w i).x0) (congrArg Lane6.x0 hSum)
  have hx1 := vcUnopened_of_sum3 e (w := fun i => (w i).x1) (congrArg Lane6.x1 hSum)
  have hx2 := vcUnopened_of_sum3 e (w := fun i => (w i).x2) (congrArg Lane6.x2 hSum)
  have hx3 := vcUnopened_of_sum3 e (w := fun i => (w i).x3) (congrArg Lane6.x3 hSum)
  have hx4 := vcUnopened_of_sum3 e (w := fun i => (w i).x4) (congrArg Lane6.x4 hSum)
  have hx5 := vcUnopened_of_sum3 e (w := fun i => (w i).x5) (congrArg Lane6.x5 hSum)
  funext i
  apply Lane6.ext
  · have h := congrFun hx0 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx1 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx2 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx3 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx4 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx5 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h

/-- Opened 2-party wire projection `(w e, w ((e + 1) % 3))`. -/
@[expose] def vcPairAt (w : VcWire3) (e : Fin 3) : Goldilocks × Goldilocks :=
  (w e, w (vcNextParty3 e))

@[expose] def vcPairAtLane6 (w : VcLane6_3) (e : Fin 3) : Lane6 × Lane6 :=
  (w e, w (vcNextParty3 e))

def vcPairAtState12 (st : VcState12_3) (e : Fin 3) : Poseidon2State12 × Poseidon2State12 :=
  (st e, st (vcNextParty3 e))

/-- 2-party public constant addition `ZkBooVerifierTape::add_const` (`blind_vc.rs:352-359`). -/
def vcPairAddConst (e : Fin 3) (x : Goldilocks × Goldilocks) (c : Goldilocks) :
    Goldilocks × Goldilocks :=
  if e = 0 then (Goldilocks.add x.1 c, x.2)
  else if vcNextParty3 e = 0 then (x.1, Goldilocks.add x.2 c)
  else x

def vcWireAddConst3 (w : VcWire3) (c : Goldilocks) : VcWire3 :=
  fun i => if i = 0 then Goldilocks.add (w 0) c else w i

@[expose] def vcConstWire3 (c : Goldilocks) : VcWire3 :=
  fun i => if i = 0 then c else Goldilocks.zero

def vcConstPair (e : Fin 3) (c : Goldilocks) : Goldilocks × Goldilocks :=
  vcPairAddConst e (Goldilocks.zero, Goldilocks.zero) c

theorem vcPairAddConst_spec (w : VcWire3) (c : Goldilocks) (e : Fin 3) :
    vcPairAddConst e (vcPairAt w e) c = vcPairAt (vcWireAddConst3 w c) e := by
  rcases e with ⟨ev, hev⟩
  have hCases : ev = 0 ∨ ev = 1 ∨ ev = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> rfl

theorem vcConstPair_spec (c : Goldilocks) (e : Fin 3) :
    vcConstPair e c = vcPairAt (vcConstWire3 c) e := by
  have hz : Goldilocks.add Goldilocks.zero c = c := by
    rw [← goldOfInt_nat Goldilocks.zero, ← goldOfInt_nat c]
    simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1; omega
  have he : e = 0 ∨ e = 1 ∨ e = 2 := by revert e; decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  rcases he with rfl | rfl | rfl
  · simp only [vcConstPair, vcPairAddConst, vcPairAt, vcConstWire3, vcNextParty3, ↓reduceIte, h10, hz]
  · simp only [vcConstPair, vcPairAddConst, vcPairAt, vcConstWire3, vcNextParty3, ↓reduceIte, h10, h20]
  · simp only [vcConstPair, vcPairAddConst, vcPairAt, vcConstWire3, vcNextParty3, ↓reduceIte, h20, hz]

private theorem vcSum3_addConst (w : VcWire3) (c : Goldilocks) :
    vcSum3 (vcWireAddConst3 w c) = Goldilocks.add (vcSum3 w) c := by
  unfold vcSum3 vcWireAddConst3
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  simp only [↓reduceIte, h1, h2]
  rw [← goldOfInt_nat (w 0), ← goldOfInt_nat (w 1), ← goldOfInt_nat (w 2), ← goldOfInt_nat c]
  simp only [goldOfInt_add]; congr 1; omega

theorem vcSum3_constWire (c : Goldilocks) :
    vcSum3 (vcConstWire3 c) = c := by
  unfold vcSum3 vcConstWire3
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  simp only [↓reduceIte, h1, h2]
  rw [← goldOfInt_nat c, ← goldOfInt_nat Goldilocks.zero]
  simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1

/-- Structured per-party gate randomness types for `"QSAG.VC.ZKBOO_R.V1"` PRG expansion. -/
abbrev SboxCoins := Goldilocks × Goldilocks × Goldilocks × Goldilocks

structure ExtRoundCoins where
  s0 : SboxCoins
  s1 : SboxCoins
  s2 : SboxCoins
  s3 : SboxCoins
  s4 : SboxCoins
  s5 : SboxCoins
  s6 : SboxCoins
  s7 : SboxCoins
  s8 : SboxCoins
  s9 : SboxCoins
  s10 : SboxCoins
  s11 : SboxCoins
  deriving DecidableEq, Repr

structure Perm12Coins where
  initExt : Vec ExtRoundCoins poseidon2InitialExtConsts.length
  internal : Vec SboxCoins poseidon2InternalConsts.length
  termExt : Vec ExtRoundCoins poseidon2TerminalExtConsts.length
  deriving DecidableEq

structure Sponge3Coins where
  perm1 : Perm12Coins
  perm2 : Perm12Coins
  perm3 : Perm12Coins
  deriving DecidableEq

structure MerkleLevelCoins where
  boolR : Goldilocks
  sel0R : Goldilocks
  sel1R : Goldilocks
  sel2R : Goldilocks
  sel3R : Goldilocks
  sel4R : Goldilocks
  sel5R : Goldilocks
  hashCoins : Sponge3Coins
  deriving DecidableEq

structure PartyGateCoins (treeDepth : Nat) where
  attrCoins : Sponge3Coins
  presCoins : Sponge3Coins
  scopeCoins : Sponge3Coins
  merkleCoins : Vec MerkleLevelCoins treeDepth
  deriving DecidableEq

/-- Expected ZKBoo multiplication share `x_e * y_e + x_e * y_{e+1} + x_{e+1} * y_e + r_e - r_{e+1}`
    (`blind_vc.rs:368-373`). -/
def vcMulExpectedPair (xe xe1 ye ye1 re re1 : Goldilocks) : Goldilocks :=
  let cross := Goldilocks.add (Goldilocks.mul xe ye)
    (Goldilocks.add (Goldilocks.mul xe ye1) (Goldilocks.mul xe1 ye))
  Goldilocks.sub (Goldilocks.add cross re) re1

def vcMulGate3 (a b r : VcWire3) : VcWire3 :=
  fun i => vcMulExpectedPair (a i) (a (vcNextParty3 i)) (b i) (b (vcNextParty3 i)) (r i) (r (vcNextParty3 i))

theorem vcMulGate3_sum (a b r : VcWire3) :
    vcSum3 (vcMulGate3 a b r) = Goldilocks.mul (vcSum3 a) (vcSum3 b) := by
  unfold vcSum3 vcMulGate3 vcMulExpectedPair vcNextParty3
  dsimp only
  rw [← goldOfInt_nat (a 0), ← goldOfInt_nat (a 1), ← goldOfInt_nat (a 2),
      ← goldOfInt_nat (b 0), ← goldOfInt_nat (b 1), ← goldOfInt_nat (b 2),
      ← goldOfInt_nat (r 0), ← goldOfInt_nat (r 1), ← goldOfInt_nat (r 2)]
  simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
  congr 1
  simp only [Int.add_mul, Int.mul_add]
  omega

structure PartyMulView where
  r : Goldilocks
  out : Goldilocks
  deriving DecidableEq, Repr

def pairCheckMul (x y : Goldilocks × Goldilocks) (gE gE1 : PartyMulView) :
    Option (Goldilocks × Goldilocks) :=
  if gE.out = vcMulExpectedPair x.1 x.2 y.1 y.2 gE.r gE1.r then
    some (gE.out, gE1.out)
  else
    none

def honestMulView3 (a b r : VcWire3) : Fin 3 → PartyMulView :=
  fun i => { r := r i, out := vcMulGate3 a b r i }

private theorem pairCheckMul_step {wx wy : VcWire3} {g : Fin 3 → PartyMulView} {e : Fin 3}
    {outP : Goldilocks × Goldilocks}
    (hOk : pairCheckMul (vcPairAt wx e) (vcPairAt wy e) (g e) (g (vcNextParty3 e)) = some outP) :
    outP = vcPairAt (fun i => (g i).out) e ∧
    (g e).out = vcMulGate3 wx wy (fun i => (g i).r) e := by
  unfold pairCheckMul vcPairAt at hOk
  dsimp only at hOk
  if hEq : (g e).out = vcMulExpectedPair (wx e) (wx (vcNextParty3 e)) (wy e) (wy (vcNextParty3 e))
      (g e).r (g (vcNextParty3 e)).r then
    rw [ite_true_of hEq] at hOk
    injection hOk with hPair
    exact ⟨hPair.symm, hEq⟩
  else
    rw [ite_false_of hEq] at hOk; cases hOk

private theorem pairCheckMul_honest (wx wy r : VcWire3) (e : Fin 3) :
    pairCheckMul (vcPairAt wx e) (vcPairAt wy e)
      (honestMulView3 wx wy r e) (honestMulView3 wx wy r (vcNextParty3 e)) =
      some (vcPairAt (vcMulGate3 wx wy r) e) := by
  unfold pairCheckMul honestMulView3 vcPairAt vcMulGate3
  dsimp only
  simp only [↓reduceIte]

private theorem pairCheckMul_extract3 {wx wy : VcWire3} {g : Fin 3 → PartyMulView}
    {o0 o1 o2 : Goldilocks × Goldilocks}
    (h0 : pairCheckMul (vcPairAt wx 0) (vcPairAt wy 0) (g 0) (g 1) = some o0)
    (h1 : pairCheckMul (vcPairAt wx 1) (vcPairAt wy 1) (g 1) (g 2) = some o1)
    (h2 : pairCheckMul (vcPairAt wx 2) (vcPairAt wy 2) (g 2) (g 0) = some o2) :
    vcSum3 (fun i => (g i).out) = Goldilocks.mul (vcSum3 wx) (vcSum3 wy) := by
  have hFun : (fun i => (g i).out) = vcMulGate3 wx wy (fun i => (g i).r) :=
    funext (BlindVc.fin3_all (pairCheckMul_step h0).2 (pairCheckMul_step h1).2 (pairCheckMul_step h2).2)
  rw [hFun, vcMulGate3_sum]

structure PartySboxView where
  g1 : PartyMulView
  g2 : PartyMulView
  g3 : PartyMulView
  g4 : PartyMulView
  deriving DecidableEq, Repr

def extractSboxCoins (sv : PartySboxView) : SboxCoins :=
  (sv.g1.r, sv.g2.r, sv.g3.r, sv.g4.r)

def pairCheckSbox (x : Goldilocks × Goldilocks) (sE sE1 : PartySboxView) :
    Option (Goldilocks × Goldilocks) :=
  match pairCheckMul x x sE.g1 sE1.g1 with
  | none => none
  | some x2 =>
    match pairCheckMul x2 x sE.g2 sE1.g2 with
    | none => none
    | some x3 =>
      match pairCheckMul x2 x2 sE.g3 sE1.g3 with
      | none => none
      | some x4 => pairCheckMul x4 x3 sE.g4 sE1.g4

def honestSboxView3 (wx : VcWire3) (sc : Fin 3 → SboxCoins) : (Fin 3 → PartySboxView) × VcWire3 :=
  let r1 : VcWire3 := fun i => (sc i).1
  let r2 : VcWire3 := fun i => (sc i).2.1
  let r3 : VcWire3 := fun i => (sc i).2.2.1
  let r4 : VcWire3 := fun i => (sc i).2.2.2
  let g1 := honestMulView3 wx wx r1
  let w2 := vcMulGate3 wx wx r1
  let g2 := honestMulView3 w2 wx r2
  let w3 := vcMulGate3 w2 wx r2
  let g3 := honestMulView3 w2 w2 r3
  let w4 := vcMulGate3 w2 w2 r3
  let g4 := honestMulView3 w4 w3 r4
  let w7 := vcMulGate3 w4 w3 r4
  (fun i => ⟨g1 i, g2 i, g3 i, g4 i⟩, w7)

private theorem extractSboxCoins_honest (wx : VcWire3) (sc : Fin 3 → SboxCoins) (i : Fin 3) :
    extractSboxCoins ((honestSboxView3 wx sc).1 i) = sc i := rfl

private theorem honestSboxView3_sum (wx : VcWire3) (sc : Fin 3 → SboxCoins) :
    vcSum3 (honestSboxView3 wx sc).2 = sbox7 (vcSum3 wx) := by
  unfold honestSboxView3 sbox7
  dsimp only
  simp only [vcMulGate3_sum]
  have hComm : ∀ u v : Goldilocks, Goldilocks.mul u v = Goldilocks.mul v u := fun u v => by
    rw [← goldOfInt_nat u, ← goldOfInt_nat v]
    simp only [goldOfInt_mul]; congr 1; exact Int.mul_comm _ _
  exact hComm _ _

private theorem pairCheckSbox_honest (wx : VcWire3) (sc : Fin 3 → SboxCoins) (e : Fin 3) :
    pairCheckSbox (vcPairAt wx e) ((honestSboxView3 wx sc).1 e) ((honestSboxView3 wx sc).1 (vcNextParty3 e)) =
      some (vcPairAt (honestSboxView3 wx sc).2 e) := by
  unfold pairCheckSbox honestSboxView3
  dsimp only
  rw [pairCheckMul_honest]; dsimp only
  rw [pairCheckMul_honest]; dsimp only
  rw [pairCheckMul_honest]; dsimp only
  rw [pairCheckMul_honest]

private theorem pairCheckSbox_step {wx : VcWire3} {sv : Fin 3 → PartySboxView} {e : Fin 3}
    {outP : Goldilocks × Goldilocks}
    (hOk : pairCheckSbox (vcPairAt wx e) (sv e) (sv (vcNextParty3 e)) = some outP) :
    outP = vcPairAt (fun i => (sv i).g4.out) e ∧
    pairCheckMul (vcPairAt wx e) (vcPairAt wx e) (sv e).g1 (sv (vcNextParty3 e)).g1 =
      some (vcPairAt (fun i => (sv i).g1.out) e) ∧
    pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt wx e) (sv e).g2 (sv (vcNextParty3 e)).g2 =
      some (vcPairAt (fun i => (sv i).g2.out) e) ∧
    pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt (fun i => (sv i).g1.out) e)
      (sv e).g3 (sv (vcNextParty3 e)).g3 = some (vcPairAt (fun i => (sv i).g3.out) e) ∧
    pairCheckMul (vcPairAt (fun i => (sv i).g3.out) e) (vcPairAt (fun i => (sv i).g2.out) e)
      (sv e).g4 (sv (vcNextParty3 e)).g4 = some (vcPairAt (fun i => (sv i).g4.out) e) := by
  unfold pairCheckSbox at hOk
  cases hm1 : pairCheckMul (vcPairAt wx e) (vcPairAt wx e) (sv e).g1 (sv (vcNextParty3 e)).g1 with
  | none => rw [hm1] at hOk; cases hOk
  | some x2 =>
    rw [hm1] at hOk; dsimp only at hOk
    obtain ⟨hx2, _⟩ := pairCheckMul_step (g := fun i => (sv i).g1) hm1
    subst hx2
    cases hm2 : pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt wx e)
        (sv e).g2 (sv (vcNextParty3 e)).g2 with
    | none => rw [hm2] at hOk; cases hOk
    | some x3 =>
      rw [hm2] at hOk; dsimp only at hOk
      obtain ⟨hx3, _⟩ := pairCheckMul_step (g := fun i => (sv i).g2) hm2
      subst hx3
      cases hm3 : pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt (fun i => (sv i).g1.out) e)
          (sv e).g3 (sv (vcNextParty3 e)).g3 with
      | none => rw [hm3] at hOk; cases hOk
      | some x4 =>
        rw [hm3] at hOk; dsimp only at hOk
        obtain ⟨hx4, _⟩ := pairCheckMul_step (g := fun i => (sv i).g3) hm3
        subst hx4
        obtain ⟨hx7, _⟩ := pairCheckMul_step (g := fun i => (sv i).g4) hOk
        subst hx7
        exact ⟨rfl, rfl, rfl, rfl, hOk⟩

private theorem pairCheckSbox_extract3 {wx : VcWire3} {sv : Fin 3 → PartySboxView}
    {o0 o1 o2 : Goldilocks × Goldilocks}
    (h0 : pairCheckSbox (vcPairAt wx 0) (sv 0) (sv 1) = some o0)
    (h1 : pairCheckSbox (vcPairAt wx 1) (sv 1) (sv 2) = some o1)
    (h2 : pairCheckSbox (vcPairAt wx 2) (sv 2) (sv 0) = some o2) :
    vcSum3 (fun i => (sv i).g4.out) = sbox7 (vcSum3 wx) := by
  obtain ⟨_, m10, m20, m30, m40⟩ := pairCheckSbox_step h0
  obtain ⟨_, m11, m21, m31, m41⟩ := pairCheckSbox_step h1
  obtain ⟨_, m12, m22, m32, m42⟩ := pairCheckSbox_step h2
  dsimp only [vcNextParty3] at m10 m20 m30 m40 m11 m21 m31 m41 m12 m22 m32 m42
  have s1 := pairCheckMul_extract3 (g := fun i => (sv i).g1) m10 m11 m12
  have s2 := pairCheckMul_extract3 (g := fun i => (sv i).g2) m20 m21 m22
  have s3 := pairCheckMul_extract3 (g := fun i => (sv i).g3) m30 m31 m32
  have s4 := pairCheckMul_extract3 (g := fun i => (sv i).g4) m40 m41 m42
  unfold sbox7
  dsimp only
  rw [s4, s3, s2, s1]
  have hComm : ∀ u v : Goldilocks, Goldilocks.mul u v = Goldilocks.mul v u := fun u v => by
    rw [← goldOfInt_nat u, ← goldOfInt_nat v]
    simp only [goldOfInt_mul]; congr 1; exact Int.mul_comm _ _
  exact hComm _ _

structure PartyExtRoundView where
  s0 : PartySboxView
  s1 : PartySboxView
  s2 : PartySboxView
  s3 : PartySboxView
  s4 : PartySboxView
  s5 : PartySboxView
  s6 : PartySboxView
  s7 : PartySboxView
  s8 : PartySboxView
  s9 : PartySboxView
  s10 : PartySboxView
  s11 : PartySboxView
  deriving DecidableEq, Repr

def extractExtRoundCoins (rv : PartyExtRoundView) : ExtRoundCoins :=
  ⟨extractSboxCoins rv.s0, extractSboxCoins rv.s1, extractSboxCoins rv.s2, extractSboxCoins rv.s3,
   extractSboxCoins rv.s4, extractSboxCoins rv.s5, extractSboxCoins rv.s6, extractSboxCoins rv.s7,
   extractSboxCoins rv.s8, extractSboxCoins rv.s9, extractSboxCoins rv.s10, extractSboxCoins rv.s11⟩

def pairCheckExtRound (e : Fin 3) (rc : Poseidon2State12)
    (vE vE1 : PartyExtRoundView) (st : Poseidon2State12 × Poseidon2State12) :
    Option (Poseidon2State12 × Poseidon2State12) :=
  let chk (f : Poseidon2State12 → Goldilocks) (sE sE1 : PartySboxView) :=
    pairCheckSbox (vcPairAddConst e (f st.1, f st.2) (f rc)) sE sE1
  match chk (·.b0.x0) vE.s0 vE1.s0, chk (·.b0.x1) vE.s1 vE1.s1,
        chk (·.b0.x2) vE.s2 vE1.s2, chk (·.b0.x3) vE.s3 vE1.s3,
        chk (·.b1.x0) vE.s4 vE1.s4, chk (·.b1.x1) vE.s5 vE1.s5,
        chk (·.b1.x2) vE.s6 vE1.s6, chk (·.b1.x3) vE.s7 vE1.s7,
        chk (·.b2.x0) vE.s8 vE1.s8, chk (·.b2.x1) vE.s9 vE1.s9,
        chk (·.b2.x2) vE.s10 vE1.s10, chk (·.b2.x3) vE.s11 vE1.s11 with
  | some y0, some y1, some y2, some y3, some y4, some y5,
    some y6, some y7, some y8, some y9, some y10, some y11 =>
    some (applyME ⟨⟨y0.1, y1.1, y2.1, y3.1⟩, ⟨y4.1, y5.1, y6.1, y7.1⟩, ⟨y8.1, y9.1, y10.1, y11.1⟩⟩,
          applyME ⟨⟨y0.2, y1.2, y2.2, y3.2⟩, ⟨y4.2, y5.2, y6.2, y7.2⟩, ⟨y8.2, y9.2, y10.2, y11.2⟩⟩)
  | _, _, _, _, _, _, _, _, _, _, _, _ => none

def vcExtRoundOut3 (rv : Fin 3 → PartyExtRoundView) : VcState12_3 :=
  fun i =>
    applyME ⟨⟨(rv i).s0.g4.out, (rv i).s1.g4.out, (rv i).s2.g4.out, (rv i).s3.g4.out⟩,
             ⟨(rv i).s4.g4.out, (rv i).s5.g4.out, (rv i).s6.g4.out, (rv i).s7.g4.out⟩,
             ⟨(rv i).s8.g4.out, (rv i).s9.g4.out, (rv i).s10.g4.out, (rv i).s11.g4.out⟩⟩

def honestExtRound3 (rc : Poseidon2State12) (st : VcState12_3) (ec : Fin 3 → ExtRoundCoins) :
    (Fin 3 → PartyExtRoundView) × VcState12_3 :=
  let mk (f : Poseidon2State12 → Goldilocks) (sel : ExtRoundCoins → SboxCoins) :=
    honestSboxView3 (vcWireAddConst3 (fun i => f (st i)) (f rc)) (fun i => sel (ec i))
  let r0 := mk (·.b0.x0) (·.s0); let r1 := mk (·.b0.x1) (·.s1)
  let r2 := mk (·.b0.x2) (·.s2); let r3 := mk (·.b0.x3) (·.s3)
  let r4 := mk (·.b1.x0) (·.s4); let r5 := mk (·.b1.x1) (·.s5)
  let r6 := mk (·.b1.x2) (·.s6); let r7 := mk (·.b1.x3) (·.s7)
  let r8 := mk (·.b2.x0) (·.s8); let r9 := mk (·.b2.x1) (·.s9)
  let r10 := mk (·.b2.x2) (·.s10); let r11 := mk (·.b2.x3) (·.s11)
  let rv : Fin 3 → PartyExtRoundView := fun i =>
    ⟨r0.1 i, r1.1 i, r2.1 i, r3.1 i, r4.1 i, r5.1 i,
     r6.1 i, r7.1 i, r8.1 i, r9.1 i, r10.1 i, r11.1 i⟩
  (rv, vcExtRoundOut3 rv)

private theorem extractExtRoundCoins_honest (rc : Poseidon2State12) (st : VcState12_3)
    (ec : Fin 3 → ExtRoundCoins) (i : Fin 3) :
    extractExtRoundCoins ((honestExtRound3 rc st ec).1 i) = ec i := rfl

private theorem pairCheckExtRound_honest (rc : Poseidon2State12) (st : VcState12_3)
    (ec : Fin 3 → ExtRoundCoins) (e : Fin 3) :
    pairCheckExtRound e rc ((honestExtRound3 rc st ec).1 e) ((honestExtRound3 rc st ec).1 (vcNextParty3 e))
      (vcPairAtState12 st e) = some (vcPairAtState12 (honestExtRound3 rc st ec).2 e) := by
  unfold pairCheckExtRound honestExtRound3 vcPairAtState12 vcExtRoundOut3
  dsimp only
  have hAt : ∀ f : Poseidon2State12 → Goldilocks,
      vcPairAddConst e (f (st e), f (st (vcNextParty3 e))) (f rc) =
        vcPairAt (vcWireAddConst3 (fun i => f (st i)) (f rc)) e :=
    fun f => vcPairAddConst_spec (fun i => f (st i)) (f rc) e
  rw [hAt (·.b0.x0), hAt (·.b0.x1), hAt (·.b0.x2), hAt (·.b0.x3),
      hAt (·.b1.x0), hAt (·.b1.x1), hAt (·.b1.x2), hAt (·.b1.x3),
      hAt (·.b2.x0), hAt (·.b2.x1), hAt (·.b2.x2), hAt (·.b2.x3),
      pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest,
      pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest,
      pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest]
  rfl

private theorem pairCheckExtRound_step {rc : Poseidon2State12} {st : VcState12_3}
    {rv : Fin 3 → PartyExtRoundView} {e : Fin 3} {outSt : Poseidon2State12 × Poseidon2State12}
    (hOk : pairCheckExtRound e rc (rv e) (rv (vcNextParty3 e)) (vcPairAtState12 st e) = some outSt) :
    outSt = vcPairAtState12 (vcExtRoundOut3 rv) e ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc.b0.x0) e) (rv e).s0 (rv (vcNextParty3 e)).s0 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x1) rc.b0.x1) e) (rv e).s1 (rv (vcNextParty3 e)).s1 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x2) rc.b0.x2) e) (rv e).s2 (rv (vcNextParty3 e)).s2 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x3) rc.b0.x3) e) (rv e).s3 (rv (vcNextParty3 e)).s3 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x0) rc.b1.x0) e) (rv e).s4 (rv (vcNextParty3 e)).s4 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x1) rc.b1.x1) e) (rv e).s5 (rv (vcNextParty3 e)).s5 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x2) rc.b1.x2) e) (rv e).s6 (rv (vcNextParty3 e)).s6 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x3) rc.b1.x3) e) (rv e).s7 (rv (vcNextParty3 e)).s7 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x0) rc.b2.x0) e) (rv e).s8 (rv (vcNextParty3 e)).s8 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x1) rc.b2.x1) e) (rv e).s9 (rv (vcNextParty3 e)).s9 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x2) rc.b2.x2) e) (rv e).s10 (rv (vcNextParty3 e)).s10 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x3) rc.b2.x3) e) (rv e).s11 (rv (vcNextParty3 e)).s11 = some o) := by
  unfold pairCheckExtRound vcPairAtState12 at hOk
  dsimp only at hOk
  have hAt : ∀ f : Poseidon2State12 → Goldilocks,
      vcPairAddConst e (f (st e), f (st (vcNextParty3 e))) (f rc) =
        vcPairAt (vcWireAddConst3 (fun i => f (st i)) (f rc)) e :=
    fun f => vcPairAddConst_spec (fun i => f (st i)) (f rc) e
  rw [hAt (·.b0.x0), hAt (·.b0.x1), hAt (·.b0.x2), hAt (·.b0.x3),
      hAt (·.b1.x0), hAt (·.b1.x1), hAt (·.b1.x2), hAt (·.b1.x3),
      hAt (·.b2.x0), hAt (·.b2.x1), hAt (·.b2.x2), hAt (·.b2.x3)] at hOk
  cases hs0 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc.b0.x0) e) (rv e).s0 (rv (vcNextParty3 e)).s0 with
  | none => rw [hs0] at hOk; cases hOk
  | some y0 =>
  cases hs1 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x1) rc.b0.x1) e) (rv e).s1 (rv (vcNextParty3 e)).s1 with
  | none => rw [hs0, hs1] at hOk; cases hOk
  | some y1 =>
  cases hs2 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x2) rc.b0.x2) e) (rv e).s2 (rv (vcNextParty3 e)).s2 with
  | none => rw [hs0, hs1, hs2] at hOk; cases hOk
  | some y2 =>
  cases hs3 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x3) rc.b0.x3) e) (rv e).s3 (rv (vcNextParty3 e)).s3 with
  | none => rw [hs0, hs1, hs2, hs3] at hOk; cases hOk
  | some y3 =>
  cases hs4 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x0) rc.b1.x0) e) (rv e).s4 (rv (vcNextParty3 e)).s4 with
  | none => rw [hs0, hs1, hs2, hs3, hs4] at hOk; cases hOk
  | some y4 =>
  cases hs5 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x1) rc.b1.x1) e) (rv e).s5 (rv (vcNextParty3 e)).s5 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5] at hOk; cases hOk
  | some y5 =>
  cases hs6 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x2) rc.b1.x2) e) (rv e).s6 (rv (vcNextParty3 e)).s6 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6] at hOk; cases hOk
  | some y6 =>
  cases hs7 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x3) rc.b1.x3) e) (rv e).s7 (rv (vcNextParty3 e)).s7 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at hOk; cases hOk
  | some y7 =>
  cases hs8 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x0) rc.b2.x0) e) (rv e).s8 (rv (vcNextParty3 e)).s8 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at hOk; cases hOk
  | some y8 =>
  cases hs9 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x1) rc.b2.x1) e) (rv e).s9 (rv (vcNextParty3 e)).s9 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9] at hOk; cases hOk
  | some y9 =>
  cases hs10 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x2) rc.b2.x2) e) (rv e).s10 (rv (vcNextParty3 e)).s10 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10] at hOk; cases hOk
  | some y10 =>
  cases hs11 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x3) rc.b2.x3) e) (rv e).s11 (rv (vcNextParty3 e)).s11 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at hOk; cases hOk
  | some y11 =>
    rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at hOk
    injection hOk with hPair
    rw [(pairCheckSbox_step (sv := fun i => (rv i).s0) hs0).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s1) hs1).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s2) hs2).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s3) hs3).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s4) hs4).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s5) hs5).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s6) hs6).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s7) hs7).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s8) hs8).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s9) hs9).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s10) hs10).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s11) hs11).1] at hPair
    exact ⟨hPair.symm, ⟨y0, rfl⟩, ⟨y1, rfl⟩, ⟨y2, rfl⟩, ⟨y3, rfl⟩, ⟨y4, rfl⟩, ⟨y5, rfl⟩,
      ⟨y6, rfl⟩, ⟨y7, rfl⟩, ⟨y8, rfl⟩, ⟨y9, rfl⟩, ⟨y10, rfl⟩, ⟨y11, rfl⟩⟩

private theorem vcSumState12_3_applyME (f : VcState12_3) :
    vcSumState12_3 (fun i => applyME (f i)) = applyME (vcSumState12_3 f) := by
  unfold vcSumState12_3
  rw [← applyME_add, ← applyME_add]

private theorem vcSumState12_3_applyMI (f : VcState12_3) :
    vcSumState12_3 (fun i => applyMI (f i)) = applyMI (vcSumState12_3 f) := by
  unfold vcSumState12_3
  rw [← applyMI_add, ← applyMI_add]

private theorem pairCheckExtRound_extract3 {rc : Poseidon2State12} {st : VcState12_3}
    {rv : Fin 3 → PartyExtRoundView} {o0 o1 o2 : Poseidon2State12 × Poseidon2State12}
    (h0 : pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) = some o0)
    (h1 : pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) = some o1)
    (h2 : pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) = some o2) :
    vcSumState12_3 (vcExtRoundOut3 rv) = externalRound rc (vcSumState12_3 st) := by
  obtain ⟨_, ⟨_, a0⟩, ⟨_, a1⟩, ⟨_, a2⟩, ⟨_, a3⟩, ⟨_, a4⟩, ⟨_, a5⟩,
             ⟨_, a6⟩, ⟨_, a7⟩, ⟨_, a8⟩, ⟨_, a9⟩, ⟨_, a10⟩, ⟨_, a11⟩⟩ := pairCheckExtRound_step h0
  obtain ⟨_, ⟨_, b0⟩, ⟨_, b1⟩, ⟨_, b2⟩, ⟨_, b3⟩, ⟨_, b4⟩, ⟨_, b5⟩,
             ⟨_, b6⟩, ⟨_, b7⟩, ⟨_, b8⟩, ⟨_, b9⟩, ⟨_, b10⟩, ⟨_, b11⟩⟩ := pairCheckExtRound_step h1
  obtain ⟨_, ⟨_, c0⟩, ⟨_, c1⟩, ⟨_, c2⟩, ⟨_, c3⟩, ⟨_, c4⟩, ⟨_, c5⟩,
             ⟨_, c6⟩, ⟨_, c7⟩, ⟨_, c8⟩, ⟨_, c9⟩, ⟨_, c10⟩, ⟨_, c11⟩⟩ := pairCheckExtRound_step h2
  dsimp only [vcNextParty3] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  dsimp only [vcNextParty3] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  dsimp only [vcNextParty3] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
  unfold vcExtRoundOut3
  rw [vcSumState12_3_applyME, externalRound_eq]
  congr 1
  rw [vcSumState12_3_lanes, sboxState12_eq, state12Add_eq, vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, lane4Add_eq]
  rw [pairCheckSbox_extract3 (sv := fun i => (rv i).s0) a0 b0 c0,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s1) a1 b1 c1,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s2) a2 b2 c2,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s3) a3 b3 c3,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s4) a4 b4 c4,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s5) a5 b5 c5,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s6) a6 b6 c6,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s7) a7 b7 c7,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s8) a8 b8 c8,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s9) a9 b9 c9,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s10) a10 b10 c10,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s11) a11 b11 c11]
  simp only [vcSum3_addConst]

def pairCheckIntRound (e : Fin 3) (rc : Goldilocks)
    (vE vE1 : PartySboxView) (st : Poseidon2State12 × Poseidon2State12) :
    Option (Poseidon2State12 × Poseidon2State12) :=
  match pairCheckSbox (vcPairAddConst e (st.1.b0.x0, st.2.b0.x0) rc) vE vE1 with
  | none => none
  | some y0 =>
    some (applyMI ⟨⟨y0.1, st.1.b0.x1, st.1.b0.x2, st.1.b0.x3⟩, st.1.b1, st.1.b2⟩,
          applyMI ⟨⟨y0.2, st.2.b0.x1, st.2.b0.x2, st.2.b0.x3⟩, st.2.b1, st.2.b2⟩)

def vcIntRoundOut3 (st : VcState12_3) (sv : Fin 3 → PartySboxView) : VcState12_3 :=
  fun i => applyMI ⟨⟨(sv i).g4.out, (st i).b0.x1, (st i).b0.x2, (st i).b0.x3⟩, (st i).b1, (st i).b2⟩

def honestIntRound3 (rc : Goldilocks) (st : VcState12_3) (sc : Fin 3 → SboxCoins) :
    (Fin 3 → PartySboxView) × VcState12_3 :=
  let r0 := honestSboxView3 (vcWireAddConst3 (fun i => (st i).b0.x0) rc) sc
  (r0.1, vcIntRoundOut3 st r0.1)

private theorem pairCheckIntRound_honest (rc : Goldilocks) (st : VcState12_3)
    (sc : Fin 3 → SboxCoins) (e : Fin 3) :
    pairCheckIntRound e rc ((honestIntRound3 rc st sc).1 e) ((honestIntRound3 rc st sc).1 (vcNextParty3 e))
      (vcPairAtState12 st e) = some (vcPairAtState12 (honestIntRound3 rc st sc).2 e) := by
  unfold pairCheckIntRound honestIntRound3 vcPairAtState12 vcIntRoundOut3
  dsimp only
  have hAdd : vcPairAddConst e ((st e).b0.x0, (st (vcNextParty3 e)).b0.x0) rc =
      vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e :=
    vcPairAddConst_spec (fun i => (st i).b0.x0) rc e
  rw [hAdd, pairCheckSbox_honest]
  rfl

private theorem pairCheckIntRound_step {rc : Goldilocks} {st : VcState12_3}
    {sv : Fin 3 → PartySboxView} {e : Fin 3} {outSt : Poseidon2State12 × Poseidon2State12}
    (hOk : pairCheckIntRound e rc (sv e) (sv (vcNextParty3 e)) (vcPairAtState12 st e) = some outSt) :
    outSt = vcPairAtState12 (vcIntRoundOut3 st sv) e ∧
    ∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e) (sv e) (sv (vcNextParty3 e)) = some o := by
  unfold pairCheckIntRound vcPairAtState12 at hOk
  dsimp only at hOk
  have hAdd : vcPairAddConst e ((st e).b0.x0, (st (vcNextParty3 e)).b0.x0) rc =
      vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e :=
    vcPairAddConst_spec (fun i => (st i).b0.x0) rc e
  rw [hAdd] at hOk
  cases hs0 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e) (sv e) (sv (vcNextParty3 e)) with
  | none => rw [hs0] at hOk; cases hOk
  | some y0 =>
    rw [hs0] at hOk
    injection hOk with hPair
    rw [(pairCheckSbox_step hs0).1] at hPair
    exact ⟨hPair.symm, ⟨y0, rfl⟩⟩

private theorem pairCheckIntRound_extract3 {rc : Goldilocks} {st : VcState12_3}
    {sv : Fin 3 → PartySboxView} {o0 o1 o2 : Poseidon2State12 × Poseidon2State12}
    (h0 : pairCheckIntRound 0 rc (sv 0) (sv 1) (vcPairAtState12 st 0) = some o0)
    (h1 : pairCheckIntRound 1 rc (sv 1) (sv 2) (vcPairAtState12 st 1) = some o1)
    (h2 : pairCheckIntRound 2 rc (sv 2) (sv 0) (vcPairAtState12 st 2) = some o2) :
    vcSumState12_3 (vcIntRoundOut3 st sv) = internalRound rc (vcSumState12_3 st) := by
  obtain ⟨_, ⟨_, a0⟩⟩ := pairCheckIntRound_step h0
  obtain ⟨_, ⟨_, b0⟩⟩ := pairCheckIntRound_step h1
  obtain ⟨_, ⟨_, c0⟩⟩ := pairCheckIntRound_step h2
  dsimp only [vcNextParty3] at a0 b0 c0
  unfold vcIntRoundOut3
  rw [vcSumState12_3_applyMI, internalRound_eq]
  congr 1
  rw [vcSumState12_3_lanes, vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq]
  rw [pairCheckSbox_extract3 a0 b0 c0, vcSum3_addConst]

def pairCheckExtRounds (e : Fin 3) :
    List Poseidon2State12 → List PartyExtRoundView → List PartyExtRoundView →
    Poseidon2State12 × Poseidon2State12 → Option (Poseidon2State12 × Poseidon2State12)
  | [], [], [], st => some st
  | rc :: rcs, vE :: vsE, vE1 :: vsE1, st =>
    match pairCheckExtRound e rc vE vE1 st with
    | none => none
    | some st' => pairCheckExtRounds e rcs vsE vsE1 st'
  | _, _, _, _ => none

def pairCheckIntRounds (e : Fin 3) :
    List Goldilocks → List PartySboxView → List PartySboxView →
    Poseidon2State12 × Poseidon2State12 → Option (Poseidon2State12 × Poseidon2State12)
  | [], [], [], st => some st
  | rc :: rcs, vE :: vsE, vE1 :: vsE1, st =>
    match pairCheckIntRound e rc vE vE1 st with
    | none => none
    | some st' => pairCheckIntRounds e rcs vsE vsE1 st'
  | _, _, _, _ => none

def honestExtRounds3 :
    (rcs : List Poseidon2State12) → VcState12_3 → (Fin 3 → Vec ExtRoundCoins rcs.length) →
    (Fin 3 → List PartyExtRoundView) × VcState12_3
  | [], st, _ => (fun _ => [], st)
  | rc :: rcs, st, cs =>
    let rHead := honestExtRound3 rc st (fun i => (cs i).head)
    let rTail := honestExtRounds3 rcs rHead.2 (fun i => (cs i).tail)
    (fun i => rHead.1 i :: rTail.1 i, rTail.2)

def honestIntRounds3 :
    (rcs : List Goldilocks) → VcState12_3 → (Fin 3 → Vec SboxCoins rcs.length) →
    (Fin 3 → List PartySboxView) × VcState12_3
  | [], st, _ => (fun _ => [], st)
  | rc :: rcs, st, cs =>
    let rHead := honestIntRound3 rc st (fun i => (cs i).head)
    let rTail := honestIntRounds3 rcs rHead.2 (fun i => (cs i).tail)
    (fun i => rHead.1 i :: rTail.1 i, rTail.2)

def extractExtRoundsCoins :
    (rcs : List Poseidon2State12) → List PartyExtRoundView → Option (Vec ExtRoundCoins rcs.length)
  | [], [] => some .nil
  | _ :: rcs, v :: vsl => (extractExtRoundsCoins rcs vsl).map (Vec.cons (extractExtRoundCoins v))
  | _, _ => none


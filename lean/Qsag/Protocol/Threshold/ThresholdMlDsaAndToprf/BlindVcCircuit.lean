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

def extractIntRoundsCoins :
    (rcs : List Goldilocks) → List PartySboxView → Option (Vec SboxCoins rcs.length)
  | [], [] => some .nil
  | _ :: rcs, v :: vsl => (extractIntRoundsCoins rcs vsl).map (Vec.cons (extractSboxCoins v))
  | _, _ => none

private theorem extractExtRoundsCoins_honest :
    ∀ (rcs : List Poseidon2State12) (st : VcState12_3) (cs : Fin 3 → Vec ExtRoundCoins rcs.length) (i : Fin 3),
      extractExtRoundsCoins rcs ((honestExtRounds3 rcs st cs).1 i) = some (cs i)
  | [], _, cs, i => by cases cs i; rfl
  | rc :: rcs, st, cs, i => by
    dsimp only [honestExtRounds3, extractExtRoundsCoins]
    rw [extractExtRoundsCoins_honest rcs (honestExtRound3 rc st (fun j => (cs j).head)).2 (fun j => (cs j).tail) i]
    dsimp only [Option.map]
    rw [extractExtRoundCoins_honest, Vec.eta_cons]

private theorem extractIntRoundsCoins_honest :
    ∀ (rcs : List Goldilocks) (st : VcState12_3) (cs : Fin 3 → Vec SboxCoins rcs.length) (i : Fin 3),
      extractIntRoundsCoins rcs ((honestIntRounds3 rcs st cs).1 i) = some (cs i)
  | [], _, cs, i => by cases cs i; rfl
  | rc :: rcs, st, cs, i => by
    dsimp only [honestIntRounds3, extractIntRoundsCoins]
    rw [extractIntRoundsCoins_honest rcs (honestIntRound3 rc st (fun j => (cs j).head)).2 (fun j => (cs j).tail) i]
    dsimp only [Option.map]
    change some (Vec.cons (cs i).head (cs i).tail) = some (cs i)
    rw [Vec.eta_cons]

private theorem pairCheckExtRounds_honest :
    ∀ (rcs : List Poseidon2State12) (st : VcState12_3) (cs : Fin 3 → Vec ExtRoundCoins rcs.length) (e : Fin 3),
      pairCheckExtRounds e rcs ((honestExtRounds3 rcs st cs).1 e)
        ((honestExtRounds3 rcs st cs).1 (vcNextParty3 e)) (vcPairAtState12 st e) =
        some (vcPairAtState12 (honestExtRounds3 rcs st cs).2 e)
  | [], _, _, _ => rfl
  | rc :: rcs, st, cs, e => by
    dsimp only [honestExtRounds3, pairCheckExtRounds]
    rw [pairCheckExtRound_honest]
    exact pairCheckExtRounds_honest rcs (honestExtRound3 rc st (fun i => (cs i).head)).2 (fun i => (cs i).tail) e

private theorem pairCheckIntRounds_honest :
    ∀ (rcs : List Goldilocks) (st : VcState12_3) (cs : Fin 3 → Vec SboxCoins rcs.length) (e : Fin 3),
      pairCheckIntRounds e rcs ((honestIntRounds3 rcs st cs).1 e)
        ((honestIntRounds3 rcs st cs).1 (vcNextParty3 e)) (vcPairAtState12 st e) =
        some (vcPairAtState12 (honestIntRounds3 rcs st cs).2 e)
  | [], _, _, _ => rfl
  | rc :: rcs, st, cs, e => by
    dsimp only [honestIntRounds3, pairCheckIntRounds]
    rw [pairCheckIntRound_honest]
    exact pairCheckIntRounds_honest rcs (honestIntRound3 rc st (fun i => (cs i).head)).2 (fun i => (cs i).tail) e

private theorem pairCheckExtRounds_extract3 :
    ∀ (rcs : List Poseidon2State12) (st : VcState12_3) (vsl : Fin 3 → List PartyExtRoundView)
      {o0 o1 o2 : Poseidon2State12 × Poseidon2State12},
      pairCheckExtRounds 0 rcs (vsl 0) (vsl 1) (vcPairAtState12 st 0) = some o0 →
      pairCheckExtRounds 1 rcs (vsl 1) (vsl 2) (vcPairAtState12 st 1) = some o1 →
      pairCheckExtRounds 2 rcs (vsl 2) (vsl 0) (vcPairAtState12 st 2) = some o2 →
      ∃ stOut : VcState12_3,
        o0 = vcPairAtState12 stOut 0 ∧
        o1 = vcPairAtState12 stOut 1 ∧
        o2 = vcPairAtState12 stOut 2 ∧
        vcSumState12_3 stOut = runRounds externalRound rcs (vcSumState12_3 st)
  | [], st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | cons _ _ => rw [hv0] at h0; cases h0
    | nil =>
      cases hv1 : vsl 1 with
      | cons _ _ => rw [hv0, hv1] at h0; cases h0
      | nil =>
        cases hv2 : vsl 2 with
        | cons _ _ => rw [hv1, hv2] at h1; cases h1
        | nil =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckExtRounds] at h0 h1 h2
          injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
          rw [runRounds_nil]
          exact ⟨st, ho0.symm, ho1.symm, ho2.symm, rfl⟩
  | rc :: rcs, st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | nil => rw [hv0] at h0; cases h0
    | cons r0 rs0 =>
      cases hv1 : vsl 1 with
      | nil => rw [hv0, hv1] at h0; cases h0
      | cons r1 rs1 =>
        cases hv2 : vsl 2 with
        | nil => rw [hv1, hv2] at h1; cases h1
        | cons r2 rs2 =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckExtRounds] at h0 h1 h2
          let rv : Fin 3 → PartyExtRoundView := fun | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2
          let rs : Fin 3 → List PartyExtRoundView := fun | ⟨0, _⟩ => rs0 | ⟨1, _⟩ => rs1 | ⟨2, _⟩ => rs2
          cases hm0 : pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with
          | none => change (match pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => _) = some o0 at h0; rw [hm0] at h0; cases h0
          | some m0 =>
            cases hm1 : pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with
            | none => change (match pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => _) = some o1 at h1; rw [hm1] at h1; cases h1
            | some m1 =>
              cases hm2 : pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with
              | none => change (match pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => _) = some o2 at h2; rw [hm2] at h2; cases h2
              | some m2 =>
                change (match pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => pairCheckExtRounds 0 rcs (rs 0) (rs 1) st') = some o0 at h0
                change (match pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => pairCheckExtRounds 1 rcs (rs 1) (rs 2) st') = some o1 at h1
                change (match pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => pairCheckExtRounds 2 rcs (rs 2) (rs 0) st') = some o2 at h2
                rw [hm0] at h0; rw [hm1] at h1; rw [hm2] at h2
                rw [(pairCheckExtRound_step hm0).1] at h0
                rw [(pairCheckExtRound_step hm1).1] at h1
                rw [(pairCheckExtRound_step hm2).1] at h2
                obtain ⟨stOut, e0, e1, e2, hSum⟩ :=
                  pairCheckExtRounds_extract3 rcs (vcExtRoundOut3 rv) rs h0 h1 h2
                rw [runRounds_cons, ← pairCheckExtRound_extract3 hm0 hm1 hm2]
                exact ⟨stOut, e0, e1, e2, hSum⟩

private theorem pairCheckIntRounds_extract3 :
    ∀ (rcs : List Goldilocks) (st : VcState12_3) (vsl : Fin 3 → List PartySboxView)
      {o0 o1 o2 : Poseidon2State12 × Poseidon2State12},
      pairCheckIntRounds 0 rcs (vsl 0) (vsl 1) (vcPairAtState12 st 0) = some o0 →
      pairCheckIntRounds 1 rcs (vsl 1) (vsl 2) (vcPairAtState12 st 1) = some o1 →
      pairCheckIntRounds 2 rcs (vsl 2) (vsl 0) (vcPairAtState12 st 2) = some o2 →
      ∃ stOut : VcState12_3,
        o0 = vcPairAtState12 stOut 0 ∧
        o1 = vcPairAtState12 stOut 1 ∧
        o2 = vcPairAtState12 stOut 2 ∧
        vcSumState12_3 stOut = runRounds internalRound rcs (vcSumState12_3 st)
  | [], st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | cons _ _ => rw [hv0] at h0; cases h0
    | nil =>
      cases hv1 : vsl 1 with
      | cons _ _ => rw [hv0, hv1] at h0; cases h0
      | nil =>
        cases hv2 : vsl 2 with
        | cons _ _ => rw [hv1, hv2] at h1; cases h1
        | nil =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckIntRounds] at h0 h1 h2
          injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
          rw [runRounds_nil]
          exact ⟨st, ho0.symm, ho1.symm, ho2.symm, rfl⟩
  | rc :: rcs, st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | nil => rw [hv0] at h0; cases h0
    | cons r0 rs0 =>
      cases hv1 : vsl 1 with
      | nil => rw [hv0, hv1] at h0; cases h0
      | cons r1 rs1 =>
        cases hv2 : vsl 2 with
        | nil => rw [hv1, hv2] at h1; cases h1
        | cons r2 rs2 =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckIntRounds] at h0 h1 h2
          let rv : Fin 3 → PartySboxView := fun | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2
          let rs : Fin 3 → List PartySboxView := fun | ⟨0, _⟩ => rs0 | ⟨1, _⟩ => rs1 | ⟨2, _⟩ => rs2
          cases hm0 : pairCheckIntRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with
          | none => change (match pairCheckIntRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => _) = some o0 at h0; rw [hm0] at h0; cases h0
          | some m0 =>
            cases hm1 : pairCheckIntRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with
            | none => change (match pairCheckIntRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => _) = some o1 at h1; rw [hm1] at h1; cases h1
            | some m1 =>
              cases hm2 : pairCheckIntRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with
              | none => change (match pairCheckIntRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => _) = some o2 at h2; rw [hm2] at h2; cases h2
              | some m2 =>
                change (match pairCheckIntRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => pairCheckIntRounds 0 rcs (rs 0) (rs 1) st') = some o0 at h0
                change (match pairCheckIntRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => pairCheckIntRounds 1 rcs (rs 1) (rs 2) st') = some o1 at h1
                change (match pairCheckIntRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => pairCheckIntRounds 2 rcs (rs 2) (rs 0) st') = some o2 at h2
                rw [hm0] at h0; rw [hm1] at h1; rw [hm2] at h2
                rw [(pairCheckIntRound_step hm0).1] at h0
                rw [(pairCheckIntRound_step hm1).1] at h1
                rw [(pairCheckIntRound_step hm2).1] at h2
                obtain ⟨stOut, e0, e1, e2, hSum⟩ :=
                  pairCheckIntRounds_extract3 rcs (vcIntRoundOut3 st rv) rs h0 h1 h2
                rw [runRounds_cons, ← pairCheckIntRound_extract3 hm0 hm1 hm2]
                exact ⟨stOut, e0, e1, e2, hSum⟩

structure PartyPerm12View where
  initExt : List PartyExtRoundView
  internal : List PartySboxView
  termExt : List PartyExtRoundView
  deriving DecidableEq, Repr

def extractPerm12Coins (pv : PartyPerm12View) : Option Perm12Coins :=
  match extractExtRoundsCoins poseidon2InitialExtConsts pv.initExt,
        extractIntRoundsCoins poseidon2InternalConsts pv.internal,
        extractExtRoundsCoins poseidon2TerminalExtConsts pv.termExt with
  | some c1, some c2, some c3 => some ⟨c1, c2, c3⟩
  | _, _, _ => none

def pairCheckRawPerm12 (e : Fin 3) (vE vE1 : PartyPerm12View)
    (st : Poseidon2State12 × Poseidon2State12) : Option (Poseidon2State12 × Poseidon2State12) :=
  let s0 := (applyME st.1, applyME st.2)
  match pairCheckExtRounds e poseidon2InitialExtConsts vE.initExt vE1.initExt s0 with
  | none => none
  | some s1 =>
    match pairCheckIntRounds e poseidon2InternalConsts vE.internal vE1.internal s1 with
    | none => none
    | some s2 => pairCheckExtRounds e poseidon2TerminalExtConsts vE.termExt vE1.termExt s2

def honestRawPerm12_3 (st : VcState12_3) (pc : Fin 3 → Perm12Coins) :
    (Fin 3 → PartyPerm12View) × VcState12_3 :=
  let s0 : VcState12_3 := fun i => applyME (st i)
  let r1 := honestExtRounds3 poseidon2InitialExtConsts s0 (fun i => (pc i).initExt)
  let r2 := honestIntRounds3 poseidon2InternalConsts r1.2 (fun i => (pc i).internal)
  let r3 := honestExtRounds3 poseidon2TerminalExtConsts r2.2 (fun i => (pc i).termExt)
  (fun i => ⟨r1.1 i, r2.1 i, r3.1 i⟩, r3.2)

private theorem extractPerm12Coins_honest (st : VcState12_3) (pc : Fin 3 → Perm12Coins) (i : Fin 3) :
    extractPerm12Coins ((honestRawPerm12_3 st pc).1 i) = some (pc i) := by
  unfold extractPerm12Coins honestRawPerm12_3
  dsimp only
  rw [extractExtRoundsCoins_honest, extractIntRoundsCoins_honest, extractExtRoundsCoins_honest]

private theorem pairCheckRawPerm12_honest (st : VcState12_3) (pc : Fin 3 → Perm12Coins) (e : Fin 3) :
    pairCheckRawPerm12 e ((honestRawPerm12_3 st pc).1 e) ((honestRawPerm12_3 st pc).1 (vcNextParty3 e))
      (vcPairAtState12 st e) = some (vcPairAtState12 (honestRawPerm12_3 st pc).2 e) := by
  unfold pairCheckRawPerm12 honestRawPerm12_3
  dsimp only
  have hs0 : (applyME (vcPairAtState12 st e).1, applyME (vcPairAtState12 st e).2) =
      vcPairAtState12 (fun i => applyME (st i)) e := rfl
  rw [hs0, pairCheckExtRounds_honest]; dsimp only
  rw [pairCheckIntRounds_honest]; dsimp only
  rw [pairCheckExtRounds_honest]

private theorem pairCheckRawPerm12_extract3 {st : VcState12_3} {pv : Fin 3 → PartyPerm12View}
    {o0 o1 o2 : Poseidon2State12 × Poseidon2State12}
    (h0 : pairCheckRawPerm12 0 (pv 0) (pv 1) (vcPairAtState12 st 0) = some o0)
    (h1 : pairCheckRawPerm12 1 (pv 1) (pv 2) (vcPairAtState12 st 1) = some o1)
    (h2 : pairCheckRawPerm12 2 (pv 2) (pv 0) (vcPairAtState12 st 2) = some o2) :
    ∃ stOut : VcState12_3,
      o0 = vcPairAtState12 stOut 0 ∧
      o1 = vcPairAtState12 stOut 1 ∧
      o2 = vcPairAtState12 stOut 2 ∧
      vcSumState12_3 stOut = poseidon2Perm12 (vcSumState12_3 st) := by
  unfold pairCheckRawPerm12 at h0 h1 h2
  let s0 : VcState12_3 := fun i => applyME (st i)
  change (match pairCheckExtRounds 0 poseidon2InitialExtConsts (pv 0).initExt (pv 1).initExt (vcPairAtState12 s0 0) with | none => none | some s1 => _) = some o0 at h0
  change (match pairCheckExtRounds 1 poseidon2InitialExtConsts (pv 1).initExt (pv 2).initExt (vcPairAtState12 s0 1) with | none => none | some s1 => _) = some o1 at h1
  change (match pairCheckExtRounds 2 poseidon2InitialExtConsts (pv 2).initExt (pv 0).initExt (vcPairAtState12 s0 2) with | none => none | some s1 => _) = some o2 at h2
  cases a0 : pairCheckExtRounds 0 poseidon2InitialExtConsts (pv 0).initExt (pv 1).initExt (vcPairAtState12 s0 0) with
  | none => rw [a0] at h0; cases h0
  | some u0 =>
  cases a1 : pairCheckExtRounds 1 poseidon2InitialExtConsts (pv 1).initExt (pv 2).initExt (vcPairAtState12 s0 1) with
  | none => rw [a1] at h1; cases h1
  | some u1 =>
  cases a2 : pairCheckExtRounds 2 poseidon2InitialExtConsts (pv 2).initExt (pv 0).initExt (vcPairAtState12 s0 2) with
  | none => rw [a2] at h2; cases h2
  | some u2 =>
    rw [a0] at h0; rw [a1] at h1; rw [a2] at h2
    obtain ⟨st1, hu0, hu1, hu2, hSum1⟩ :=
      pairCheckExtRounds_extract3 poseidon2InitialExtConsts s0 (fun i => (pv i).initExt) a0 a1 a2
    rw [hu0] at h0; rw [hu1] at h1; rw [hu2] at h2
    dsimp only at h0 h1 h2
    cases b0 : pairCheckIntRounds 0 poseidon2InternalConsts (pv 0).internal (pv 1).internal (vcPairAtState12 st1 0) with
    | none => rw [b0] at h0; cases h0
    | some v0 =>
    cases b1 : pairCheckIntRounds 1 poseidon2InternalConsts (pv 1).internal (pv 2).internal (vcPairAtState12 st1 1) with
    | none => rw [b1] at h1; cases h1
    | some v1 =>
    cases b2 : pairCheckIntRounds 2 poseidon2InternalConsts (pv 2).internal (pv 0).internal (vcPairAtState12 st1 2) with
    | none => rw [b2] at h2; cases h2
    | some v2 =>
      rw [b0] at h0; rw [b1] at h1; rw [b2] at h2
      obtain ⟨st2, hv0, hv1, hv2, hSum2⟩ :=
        pairCheckIntRounds_extract3 poseidon2InternalConsts st1 (fun i => (pv i).internal) b0 b1 b2
      rw [hv0] at h0; rw [hv1] at h1; rw [hv2] at h2
      dsimp only at h0 h1 h2
      obtain ⟨st3, hw0, hw1, hw2, hSum3⟩ :=
        pairCheckExtRounds_extract3 poseidon2TerminalExtConsts st2 (fun i => (pv i).termExt) h0 h1 h2
      refine ⟨st3, hw0, hw1, hw2, ?_⟩
      unfold poseidon2Perm12
      dsimp only
      rw [hSum3, hSum2, hSum1, vcSumState12_3_applyME]

/-- Single party's view for 3-permutation rate-6/capacity-6 `absorbRate6Sponge3` (`blind_vc.rs:390-405`). -/
structure PartySponge3PermView where
  perm1 : PartyPerm12View
  perm2 : PartyPerm12View
  perm3 : PartyPerm12View
  deriving DecidableEq, Repr

def extractSponge3Coins (sv : PartySponge3PermView) : Option Sponge3Coins :=
  match extractPerm12Coins sv.perm1, extractPerm12Coins sv.perm2, extractPerm12Coins sv.perm3 with
  | some c1, some c2, some c3 => some ⟨c1, c2, c3⟩
  | _, _, _ => none

def pairCheckSponge3Perm (e : Fin 3) (vE vE1 : PartySponge3PermView)
    (c0 c1 c2 : Lane6 × Lane6) : Option (Lane6 × Lane6) :=
  let s1 := (mkState12Of6 c0.1 lane6Zero, mkState12Of6 c0.2 lane6Zero)
  match pairCheckRawPerm12 e vE.perm1 vE1.perm1 s1 with
  | none => none
  | some p1 =>
    let s2 := (mkState12Of6 (lane6Add (state12Rate6 p1.1) c1.1) (state12Cap6 p1.1),
               mkState12Of6 (lane6Add (state12Rate6 p1.2) c1.2) (state12Cap6 p1.2))
    match pairCheckRawPerm12 e vE.perm2 vE1.perm2 s2 with
    | none => none
    | some p2 =>
      let s3 := (mkState12Of6 (lane6Add (state12Rate6 p2.1) c2.1) (state12Cap6 p2.1),
                 mkState12Of6 (lane6Add (state12Rate6 p2.2) c2.2) (state12Cap6 p2.2))
      match pairCheckRawPerm12 e vE.perm3 vE1.perm3 s3 with
      | none => none
      | some p3 => some (state12Rate6 p3.1, state12Rate6 p3.2)

def honestSponge3Perm3 (c0 c1 c2 : VcLane6_3) (sc : Fin 3 → Sponge3Coins) :
    (Fin 3 → PartySponge3PermView) × VcLane6_3 :=
  let s1 : VcState12_3 := fun i => mkState12Of6 (c0 i) lane6Zero
  let r1 := honestRawPerm12_3 s1 (fun i => (sc i).perm1)
  let s2 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (r1.2 i)) (c1 i)) (state12Cap6 (r1.2 i))
  let r2 := honestRawPerm12_3 s2 (fun i => (sc i).perm2)
  let s3 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (r2.2 i)) (c2 i)) (state12Cap6 (r2.2 i))
  let r3 := honestRawPerm12_3 s3 (fun i => (sc i).perm3)
  (fun i => ⟨r1.1 i, r2.1 i, r3.1 i⟩, fun i => state12Rate6 (r3.2 i))

private theorem extractSponge3Coins_honest (c0 c1 c2 : VcLane6_3) (sc : Fin 3 → Sponge3Coins) (i : Fin 3) :
    extractSponge3Coins ((honestSponge3Perm3 c0 c1 c2 sc).1 i) = some (sc i) := by
  unfold extractSponge3Coins honestSponge3Perm3
  dsimp only
  rw [extractPerm12Coins_honest, extractPerm12Coins_honest, extractPerm12Coins_honest]

private theorem pairCheckSponge3Perm_honest (c0 c1 c2 : VcLane6_3)
    (sc : Fin 3 → Sponge3Coins) (e : Fin 3) :
    pairCheckSponge3Perm e ((honestSponge3Perm3 c0 c1 c2 sc).1 e)
      ((honestSponge3Perm3 c0 c1 c2 sc).1 (vcNextParty3 e))
      (vcPairAtLane6 c0 e) (vcPairAtLane6 c1 e) (vcPairAtLane6 c2 e) =
      some (vcPairAtLane6 (honestSponge3Perm3 c0 c1 c2 sc).2 e) := by
  unfold pairCheckSponge3Perm honestSponge3Perm3 vcPairAtLane6
  dsimp only
  have hs1 : (mkState12Of6 (c0 e) lane6Zero, mkState12Of6 (c0 (vcNextParty3 e)) lane6Zero) =
      vcPairAtState12 (fun i => mkState12Of6 (c0 i) lane6Zero) e := rfl
  rw [hs1, pairCheckRawPerm12_honest]; dsimp only
  let p1 := (honestRawPerm12_3 (fun i => mkState12Of6 (c0 i) lane6Zero) (fun i => (sc i).perm1)).2
  have hs2 : (mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p1 e).1) (c1 e)) (state12Cap6 (vcPairAtState12 p1 e).1),
              mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p1 e).2) (c1 (vcNextParty3 e))) (state12Cap6 (vcPairAtState12 p1 e).2)) =
      vcPairAtState12 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))) e := rfl
  rw [hs2, pairCheckRawPerm12_honest]; dsimp only
  let p2 := (honestRawPerm12_3 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))) (fun i => (sc i).perm2)).2
  have hs3 : (mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p2 e).1) (c2 e)) (state12Cap6 (vcPairAtState12 p2 e).1),
              mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p2 e).2) (c2 (vcNextParty3 e))) (state12Cap6 (vcPairAtState12 p2 e).2)) =
      vcPairAtState12 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p2 i)) (c2 i)) (state12Cap6 (p2 i))) e := rfl
  rw [hs3, pairCheckRawPerm12_honest]
  rfl

theorem pairCheckSponge3Perm_extract3 {c0 c1 c2 : VcLane6_3}
    {sv : Fin 3 → PartySponge3PermView} {o0 o1 o2 : Lane6 × Lane6}
    (h0 : pairCheckSponge3Perm 0 (sv 0) (sv 1) (vcPairAtLane6 c0 0) (vcPairAtLane6 c1 0) (vcPairAtLane6 c2 0) = some o0)
    (h1 : pairCheckSponge3Perm 1 (sv 1) (sv 2) (vcPairAtLane6 c0 1) (vcPairAtLane6 c1 1) (vcPairAtLane6 c2 1) = some o1)
    (h2 : pairCheckSponge3Perm 2 (sv 2) (sv 0) (vcPairAtLane6 c0 2) (vcPairAtLane6 c1 2) (vcPairAtLane6 c2 2) = some o2) :
    ∃ out6 : VcLane6_3,
      o0 = vcPairAtLane6 out6 0 ∧
      o1 = vcPairAtLane6 out6 1 ∧
      o2 = vcPairAtLane6 out6 2 ∧
      vcSumLane6_3 out6 =
        state12Rate6 (absorbRate6Sponge3 (vcSumLane6_3 c0) (vcSumLane6_3 c1) (vcSumLane6_3 c2)) := by
  unfold pairCheckSponge3Perm at h0 h1 h2
  let s1 : VcState12_3 := fun i => mkState12Of6 (c0 i) lane6Zero
  change (match pairCheckRawPerm12 0 (sv 0).perm1 (sv 1).perm1 (vcPairAtState12 s1 0) with | none => none | some p1 => _) = some o0 at h0
  change (match pairCheckRawPerm12 1 (sv 1).perm1 (sv 2).perm1 (vcPairAtState12 s1 1) with | none => none | some p1 => _) = some o1 at h1
  change (match pairCheckRawPerm12 2 (sv 2).perm1 (sv 0).perm1 (vcPairAtState12 s1 2) with | none => none | some p1 => _) = some o2 at h2
  cases a0 : pairCheckRawPerm12 0 (sv 0).perm1 (sv 1).perm1 (vcPairAtState12 s1 0) with
  | none => rw [a0] at h0; cases h0
  | some u0 =>
  cases a1 : pairCheckRawPerm12 1 (sv 1).perm1 (sv 2).perm1 (vcPairAtState12 s1 1) with
  | none => rw [a1] at h1; cases h1
  | some u1 =>
  cases a2 : pairCheckRawPerm12 2 (sv 2).perm1 (sv 0).perm1 (vcPairAtState12 s1 2) with
  | none => rw [a2] at h2; cases h2
  | some u2 =>
    rw [a0] at h0; rw [a1] at h1; rw [a2] at h2
    obtain ⟨p1, hu0, hu1, hu2, hSum1⟩ :=
      pairCheckRawPerm12_extract3 (pv := fun i => (sv i).perm1) a0 a1 a2
    rw [hu0] at h0; rw [hu1] at h1; rw [hu2] at h2
    dsimp only at h0 h1 h2
    let s2 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))
    change (match pairCheckRawPerm12 0 (sv 0).perm2 (sv 1).perm2 (vcPairAtState12 s2 0) with | none => none | some p2 => _) = some o0 at h0
    change (match pairCheckRawPerm12 1 (sv 1).perm2 (sv 2).perm2 (vcPairAtState12 s2 1) with | none => none | some p2 => _) = some o1 at h1
    change (match pairCheckRawPerm12 2 (sv 2).perm2 (sv 0).perm2 (vcPairAtState12 s2 2) with | none => none | some p2 => _) = some o2 at h2
    cases b0 : pairCheckRawPerm12 0 (sv 0).perm2 (sv 1).perm2 (vcPairAtState12 s2 0) with
    | none => rw [b0] at h0; cases h0
    | some v0 =>
    cases b1 : pairCheckRawPerm12 1 (sv 1).perm2 (sv 2).perm2 (vcPairAtState12 s2 1) with
    | none => rw [b1] at h1; cases h1
    | some v1 =>
    cases b2 : pairCheckRawPerm12 2 (sv 2).perm2 (sv 0).perm2 (vcPairAtState12 s2 2) with
    | none => rw [b2] at h2; cases h2
    | some v2 =>
      rw [b0] at h0; rw [b1] at h1; rw [b2] at h2
      obtain ⟨p2, hv0, hv1, hv2, hSum2⟩ :=
        pairCheckRawPerm12_extract3 (pv := fun i => (sv i).perm2) b0 b1 b2
      rw [hv0] at h0; rw [hv1] at h1; rw [hv2] at h2
      dsimp only at h0 h1 h2
      let s3 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (p2 i)) (c2 i)) (state12Cap6 (p2 i))
      change (match pairCheckRawPerm12 0 (sv 0).perm3 (sv 1).perm3 (vcPairAtState12 s3 0) with | none => none | some p3 => _) = some o0 at h0
      change (match pairCheckRawPerm12 1 (sv 1).perm3 (sv 2).perm3 (vcPairAtState12 s3 1) with | none => none | some p3 => _) = some o1 at h1
      change (match pairCheckRawPerm12 2 (sv 2).perm3 (sv 0).perm3 (vcPairAtState12 s3 2) with | none => none | some p3 => _) = some o2 at h2
      cases d0 : pairCheckRawPerm12 0 (sv 0).perm3 (sv 1).perm3 (vcPairAtState12 s3 0) with
      | none => rw [d0] at h0; cases h0
      | some w0 =>
      cases d1 : pairCheckRawPerm12 1 (sv 1).perm3 (sv 2).perm3 (vcPairAtState12 s3 1) with
      | none => rw [d1] at h1; cases h1
      | some w1 =>
      cases d2 : pairCheckRawPerm12 2 (sv 2).perm3 (sv 0).perm3 (vcPairAtState12 s3 2) with
      | none => rw [d2] at h2; cases h2
      | some w2 =>
        rw [d0] at h0; rw [d1] at h1; rw [d2] at h2
        obtain ⟨p3, hw0, hw1, hw2, hSum3⟩ :=
          pairCheckRawPerm12_extract3 (pv := fun i => (sv i).perm3) d0 d1 d2
        rw [hw0] at h0; rw [hw1] at h1; rw [hw2] at h2
        injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
        refine ⟨fun i => state12Rate6 (p3 i), ho0.symm, ho1.symm, ho2.symm, ?_⟩
        rw [← state12Rate6_vcSum, hSum3]
        have hs1Eq : vcSumState12_3 s1 = mkState12Of6 (vcSumLane6_3 c0) lane6Zero := by
          dsimp only [s1]; rw [vcSumState12_3_of6, vcSumLane6_3_zero]
        have hs2Eq : vcSumState12_3 s2 =
            mkState12Of6 (lane6Add (state12Rate6 (vcSumState12_3 p1)) (vcSumLane6_3 c1))
              (state12Cap6 (vcSumState12_3 p1)) := by
          dsimp only [s2]
          rw [vcSumState12_3_of6, vcSumLane6_3_add, ← state12Rate6_vcSum, ← state12Cap6_vcSum]
        have hs3Eq : vcSumState12_3 s3 =
            mkState12Of6 (lane6Add (state12Rate6 (vcSumState12_3 p2)) (vcSumLane6_3 c2))
              (state12Cap6 (vcSumState12_3 p2)) := by
          dsimp only [s3]
          rw [vcSumState12_3_of6, vcSumLane6_3_add, ← state12Rate6_vcSum, ← state12Cap6_vcSum]
        rw [hs3Eq, hSum2, hs2Eq, hSum1, hs1Eq]
        rfl

theorem honestSponge3Perm3_sum (c0 c1 c2 : VcLane6_3) (sc : Fin 3 → Sponge3Coins) :
    vcSumLane6_3 (honestSponge3Perm3 c0 c1 c2 sc).2 =
      state12Rate6 (absorbRate6Sponge3 (vcSumLane6_3 c0) (vcSumLane6_3 c1) (vcSumLane6_3 c2)) := by
  have h0 := pairCheckSponge3Perm_honest c0 c1 c2 sc 0
  have h1 := pairCheckSponge3Perm_honest c0 c1 c2 sc 1
  have h2 := pairCheckSponge3Perm_honest c0 c1 c2 sc 2
  obtain ⟨out6, e0, e1, _, hSum⟩ := pairCheckSponge3Perm_extract3 h0 h1 h2
  have hEq : (honestSponge3Perm3 c0 c1 c2 sc).2 = out6 := by
    apply funext
    refine BlindVc.fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1)
  rwa [hEq]

/-- Single party's view for one 6-limb Merkle accumulator level (`blind_vc.rs:1993-2038`). -/
structure PartyMerkleLevelView where
  bitShare : Goldilocks
  sibShare : Lane6
  boolGate : PartyMulView
  sel0 : PartyMulView
  sel1 : PartyMulView
  sel2 : PartyMulView
  sel3 : PartyMulView
  sel4 : PartyMulView
  sel5 : PartyMulView
  hashView : PartySponge3PermView
  deriving DecidableEq, Repr

def extractMerkleLevelCoins (lv : PartyMerkleLevelView) : Option MerkleLevelCoins :=
  (extractSponge3Coins lv.hashView).map (fun hc =>
    ⟨lv.boolGate.r, lv.sel0.r, lv.sel1.r, lv.sel2.r, lv.sel3.r, lv.sel4.r, lv.sel5.r, hc⟩)

def pairSubGold (a b : Goldilocks × Goldilocks) : Goldilocks × Goldilocks :=
  (Goldilocks.sub a.1 b.1, Goldilocks.sub a.2 b.2)

def pairAddGold (a b : Goldilocks × Goldilocks) : Goldilocks × Goldilocks :=
  (Goldilocks.add a.1 b.1, Goldilocks.add a.2 b.2)

/-- Verify one 6-limb Merkle level at challenge `e`, returning `(nextCurNodePair, boolZeroPair)`. -/
def pairCheckMerkleLevel (e : Fin 3) (epoch : UInt64) (layer : Nat)
    (cur : Lane6 × Lane6) (lvE lvE1 : PartyMerkleLevelView) :
    Option ((Lane6 × Lane6) × (Goldilocks × Goldilocks)) :=
  let b := (lvE.bitShare, lvE1.bitShare)
  let oneWire := vcConstPair e Goldilocks.one
  let oneMinusB := pairSubGold oneWire b
  match pairCheckMul b oneMinusB lvE.boolGate lvE1.boolGate with
  | none => none
  | some boolZero =>
    let d0 := pairSubGold (lvE.sibShare.x0, lvE1.sibShare.x0) (cur.1.x0, cur.2.x0)
    let d1 := pairSubGold (lvE.sibShare.x1, lvE1.sibShare.x1) (cur.1.x1, cur.2.x1)
    let d2 := pairSubGold (lvE.sibShare.x2, lvE1.sibShare.x2) (cur.1.x2, cur.2.x2)
    let d3 := pairSubGold (lvE.sibShare.x3, lvE1.sibShare.x3) (cur.1.x3, cur.2.x3)
    let d4 := pairSubGold (lvE.sibShare.x4, lvE1.sibShare.x4) (cur.1.x4, cur.2.x4)
    let d5 := pairSubGold (lvE.sibShare.x5, lvE1.sibShare.x5) (cur.1.x5, cur.2.x5)
    match pairCheckMul b d0 lvE.sel0 lvE1.sel0,
          pairCheckMul b d1 lvE.sel1 lvE1.sel1,
          pairCheckMul b d2 lvE.sel2 lvE1.sel2,
          pairCheckMul b d3 lvE.sel3 lvE1.sel3,
          pairCheckMul b d4 lvE.sel4 lvE1.sel4,
          pairCheckMul b d5 lvE.sel5 lvE1.sel5 with
    | some del0, some del1, some del2, some del3, some del4, some del5 =>
      let l0 := pairAddGold (cur.1.x0, cur.2.x0) del0
      let l1 := pairAddGold (cur.1.x1, cur.2.x1) del1
      let l2 := pairAddGold (cur.1.x2, cur.2.x2) del2
      let l3 := pairAddGold (cur.1.x3, cur.2.x3) del3
      let l4 := pairAddGold (cur.1.x4, cur.2.x4) del4
      let l5 := pairAddGold (cur.1.x5, cur.2.x5) del5
      let r0 := pairSubGold (lvE.sibShare.x0, lvE1.sibShare.x0) del0
      let r1 := pairSubGold (lvE.sibShare.x1, lvE1.sibShare.x1) del1
      let r2 := pairSubGold (lvE.sibShare.x2, lvE1.sibShare.x2) del2
      let r3 := pairSubGold (lvE.sibShare.x3, lvE1.sibShare.x3) del3
      let r4 := pairSubGold (lvE.sibShare.x4, lvE1.sibShare.x4) del4
      let r5 := pairSubGold (lvE.sibShare.x5, lvE1.sibShare.x5) del5
      let k0 := vcConstPair e (vcSchemaLo epoch)
      let k1 := vcConstPair e (Goldilocks.ofNat layer)
      let k2 := vcConstPair e (Goldilocks.ofNat vcMerkleNodeTag.toNat)
      let k3 := vcConstPair e (vcSchemaHiWithTag epoch poseidon2ConstIV)
      let k4 := vcConstPair e Goldilocks.one
      let c0Pair : Lane6 × Lane6 := (⟨l0.1, l1.1, l2.1, l3.1, l4.1, l5.1⟩, ⟨l0.2, l1.2, l2.2, l3.2, l4.2, l5.2⟩)
      let c1Pair : Lane6 × Lane6 := (⟨r0.1, r1.1, r2.1, r3.1, r4.1, r5.1⟩, ⟨r0.2, r1.2, r2.2, r3.2, r4.2, r5.2⟩)
      let c2Pair : Lane6 × Lane6 :=
        (⟨k0.1, k1.1, k2.1, k3.1, k4.1, Goldilocks.zero⟩,
         ⟨k0.2, k1.2, k2.2, k3.2, k4.2, Goldilocks.zero⟩)
      match pairCheckSponge3Perm e lvE.hashView lvE1.hashView c0Pair c1Pair c2Pair with
      | none => none
      | some nextPair => some (nextPair, boolZero)
    | _, _, _, _, _, _ => none

def honestMerkleLevel3 (epoch : UInt64) (layer : Nat) (cur : VcLane6_3)
    (b : VcWire3) (sib : VcLane6_3) (mc : Fin 3 → MerkleLevelCoins) :
    (Fin 3 → PartyMerkleLevelView) × VcLane6_3 × VcWire3 :=
  let oneMinusB : VcWire3 := fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (b i)
  let bg := honestMulView3 b oneMinusB (fun i => (mc i).boolR)
  let bz := vcMulGate3 b oneMinusB (fun i => (mc i).boolR)
  let d0 : VcWire3 := fun i => Goldilocks.sub (sib i).x0 (cur i).x0
  let d1 : VcWire3 := fun i => Goldilocks.sub (sib i).x1 (cur i).x1
  let d2 : VcWire3 := fun i => Goldilocks.sub (sib i).x2 (cur i).x2
  let d3 : VcWire3 := fun i => Goldilocks.sub (sib i).x3 (cur i).x3
  let d4 : VcWire3 := fun i => Goldilocks.sub (sib i).x4 (cur i).x4
  let d5 : VcWire3 := fun i => Goldilocks.sub (sib i).x5 (cur i).x5
  let s0 := honestMulView3 b d0 (fun i => (mc i).sel0R); let del0 := vcMulGate3 b d0 (fun i => (mc i).sel0R)
  let s1 := honestMulView3 b d1 (fun i => (mc i).sel1R); let del1 := vcMulGate3 b d1 (fun i => (mc i).sel1R)
  let s2 := honestMulView3 b d2 (fun i => (mc i).sel2R); let del2 := vcMulGate3 b d2 (fun i => (mc i).sel2R)
  let s3 := honestMulView3 b d3 (fun i => (mc i).sel3R); let del3 := vcMulGate3 b d3 (fun i => (mc i).sel3R)
  let s4 := honestMulView3 b d4 (fun i => (mc i).sel4R); let del4 := vcMulGate3 b d4 (fun i => (mc i).sel4R)
  let s5 := honestMulView3 b d5 (fun i => (mc i).sel5R); let del5 := vcMulGate3 b d5 (fun i => (mc i).sel5R)
  let c0 : VcLane6_3 := fun i =>
    ⟨Goldilocks.add (cur i).x0 (del0 i), Goldilocks.add (cur i).x1 (del1 i),
     Goldilocks.add (cur i).x2 (del2 i), Goldilocks.add (cur i).x3 (del3 i),
     Goldilocks.add (cur i).x4 (del4 i), Goldilocks.add (cur i).x5 (del5 i)⟩
  let c1 : VcLane6_3 := fun i =>
    ⟨Goldilocks.sub (sib i).x0 (del0 i), Goldilocks.sub (sib i).x1 (del1 i),
     Goldilocks.sub (sib i).x2 (del2 i), Goldilocks.sub (sib i).x3 (del3 i),
     Goldilocks.sub (sib i).x4 (del4 i), Goldilocks.sub (sib i).x5 (del5 i)⟩
  let c2 : VcLane6_3 := fun i =>
    ⟨vcConstWire3 (vcSchemaLo epoch) i,
     vcConstWire3 (Goldilocks.ofNat layer) i,
     vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
     vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
     vcConstWire3 Goldilocks.one i,
     Goldilocks.zero⟩
  let sp := honestSponge3Perm3 c0 c1 c2 (fun i => (mc i).hashCoins)
  (fun i => ⟨b i, sib i, bg i, s0 i, s1 i, s2 i, s3 i, s4 i, s5 i, sp.1 i⟩, sp.2, bz)

private theorem extractMerkleLevelCoins_honest (epoch : UInt64) (layer : Nat) (cur : VcLane6_3)
    (b : VcWire3) (sib : VcLane6_3) (mc : Fin 3 → MerkleLevelCoins) (i : Fin 3) :
    extractMerkleLevelCoins ((honestMerkleLevel3 epoch layer cur b sib mc).1 i) = some (mc i) := by
  unfold extractMerkleLevelCoins honestMerkleLevel3 honestMulView3
  dsimp only
  simp only [extractSponge3Coins_honest, Option.map]

theorem pairCheckMerkleLevel_honest (epoch : UInt64) (layer : Nat)
    (cur : VcLane6_3) (b : VcWire3) (sib : VcLane6_3) (mc : Fin 3 → MerkleLevelCoins) (e : Fin 3) :
    pairCheckMerkleLevel e epoch layer (vcPairAtLane6 cur e)
      ((honestMerkleLevel3 epoch layer cur b sib mc).1 e)
      ((honestMerkleLevel3 epoch layer cur b sib mc).1 (vcNextParty3 e)) =
      some (vcPairAtLane6 (honestMerkleLevel3 epoch layer cur b sib mc).2.1 e,
            vcPairAt (honestMerkleLevel3 epoch layer cur b sib mc).2.2 e) := by
  unfold pairCheckMerkleLevel honestMerkleLevel3 vcPairAtLane6
  dsimp only
  rw [vcConstPair_spec Goldilocks.one e,
      vcConstPair_spec (vcSchemaLo epoch) e,
      vcConstPair_spec (Goldilocks.ofNat layer) e,
      vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) e,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) e]
  have hOneSub : pairSubGold (vcPairAt (vcConstWire3 Goldilocks.one) e) (b e, b (vcNextParty3 e)) =
      vcPairAt (fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (b i)) e := rfl
  have hbPair : (b e, b (vcNextParty3 e)) = vcPairAt b e := rfl
  have hd0 : pairSubGold ((sib e).x0, (sib (vcNextParty3 e)).x0) ((cur e).x0, (cur (vcNextParty3 e)).x0) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x0 (cur i).x0) e := rfl
  have hd1 : pairSubGold ((sib e).x1, (sib (vcNextParty3 e)).x1) ((cur e).x1, (cur (vcNextParty3 e)).x1) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x1 (cur i).x1) e := rfl
  have hd2 : pairSubGold ((sib e).x2, (sib (vcNextParty3 e)).x2) ((cur e).x2, (cur (vcNextParty3 e)).x2) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x2 (cur i).x2) e := rfl
  have hd3 : pairSubGold ((sib e).x3, (sib (vcNextParty3 e)).x3) ((cur e).x3, (cur (vcNextParty3 e)).x3) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x3 (cur i).x3) e := rfl
  have hd4 : pairSubGold ((sib e).x4, (sib (vcNextParty3 e)).x4) ((cur e).x4, (cur (vcNextParty3 e)).x4) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x4 (cur i).x4) e := rfl
  have hd5 : pairSubGold ((sib e).x5, (sib (vcNextParty3 e)).x5) ((cur e).x5, (cur (vcNextParty3 e)).x5) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x5 (cur i).x5) e := rfl
  rw [hOneSub, hbPair, pairCheckMul_honest, hd0, hd1, hd2, hd3, hd4, hd5,
      pairCheckMul_honest, pairCheckMul_honest, pairCheckMul_honest,
      pairCheckMul_honest, pairCheckMul_honest, pairCheckMul_honest]
  dsimp only
  have hsp := pairCheckSponge3Perm_honest
    (fun i =>
      ⟨Goldilocks.add (cur i).x0 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x0 (cur k).x0) (fun k => (mc k).sel0R) i),
       Goldilocks.add (cur i).x1 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x1 (cur k).x1) (fun k => (mc k).sel1R) i),
       Goldilocks.add (cur i).x2 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x2 (cur k).x2) (fun k => (mc k).sel2R) i),
       Goldilocks.add (cur i).x3 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x3 (cur k).x3) (fun k => (mc k).sel3R) i),
       Goldilocks.add (cur i).x4 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x4 (cur k).x4) (fun k => (mc k).sel4R) i),
       Goldilocks.add (cur i).x5 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x5 (cur k).x5) (fun k => (mc k).sel5R) i)⟩)
    (fun i =>
      ⟨Goldilocks.sub (sib i).x0 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x0 (cur k).x0) (fun k => (mc k).sel0R) i),
       Goldilocks.sub (sib i).x1 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x1 (cur k).x1) (fun k => (mc k).sel1R) i),
       Goldilocks.sub (sib i).x2 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x2 (cur k).x2) (fun k => (mc k).sel2R) i),
       Goldilocks.sub (sib i).x3 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x3 (cur k).x3) (fun k => (mc k).sel3R) i),
       Goldilocks.sub (sib i).x4 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x4 (cur k).x4) (fun k => (mc k).sel4R) i),
       Goldilocks.sub (sib i).x5 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x5 (cur k).x5) (fun k => (mc k).sel5R) i)⟩)
    (fun i =>
      ⟨vcConstWire3 (vcSchemaLo epoch) i,
       vcConstWire3 (Goldilocks.ofNat layer) i,
       vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
       vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
       vcConstWire3 Goldilocks.one i,
       Goldilocks.zero⟩)
    (fun i => (mc i).hashCoins) e
  dsimp only [vcPairAtLane6, pairAddGold, pairSubGold, vcPairAt] at hsp ⊢
  rw [hsp]

theorem pairCheckMerkleLevel_extract3 {epoch : UInt64} {layer : Nat}
    {cur : VcLane6_3} {lv : Fin 3 → PartyMerkleLevelView}
    {o0 o1 o2 : (Lane6 × Lane6) × (Goldilocks × Goldilocks)}
    (h0 : pairCheckMerkleLevel 0 epoch layer (vcPairAtLane6 cur 0) (lv 0) (lv 1) = some o0)
    (h1 : pairCheckMerkleLevel 1 epoch layer (vcPairAtLane6 cur 1) (lv 1) (lv 2) = some o1)
    (h2 : pairCheckMerkleLevel 2 epoch layer (vcPairAtLane6 cur 2) (lv 2) (lv 0) = some o2) :
    ∃ (nextCur : VcLane6_3) (bz : VcWire3),
      o0 = (vcPairAtLane6 nextCur 0, vcPairAt bz 0) ∧
      o1 = (vcPairAtLane6 nextCur 1, vcPairAt bz 1) ∧
      o2 = (vcPairAtLane6 nextCur 2, vcPairAt bz 2) ∧
      vcSum3 bz = Goldilocks.mul (vcSum3 (fun i => (lv i).bitShare))
        (Goldilocks.sub Goldilocks.one (vcSum3 (fun i => (lv i).bitShare))) ∧
      vcSumLane6_3 nextCur =
        vcMerkleStepArith epoch layer (vcSumLane6_3 cur)
          (vcSumLane6_3 (fun i => (lv i).sibShare)) (vcSum3 (fun i => (lv i).bitShare)) := by
  unfold pairCheckMerkleLevel at h0 h1 h2
  rw [vcConstPair_spec Goldilocks.one 0, vcConstPair_spec (vcSchemaLo epoch) 0,
      vcConstPair_spec (Goldilocks.ofNat layer) 0, vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) 0,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) 0] at h0
  rw [vcConstPair_spec Goldilocks.one 1, vcConstPair_spec (vcSchemaLo epoch) 1,
      vcConstPair_spec (Goldilocks.ofNat layer) 1, vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) 1,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) 1] at h1
  rw [vcConstPair_spec Goldilocks.one 2, vcConstPair_spec (vcSchemaLo epoch) 2,
      vcConstPair_spec (Goldilocks.ofNat layer) 2, vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) 2,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) 2] at h2
  let bw : VcWire3 := fun i => (lv i).bitShare
  let omb : VcWire3 := fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (bw i)
  dsimp only [vcPairAtLane6, vcPairAt, vcNextParty3, pairSubGold, pairAddGold] at h0 h1 h2
  cases hb0 : pairCheckMul (vcPairAt bw 0) (vcPairAt omb 0) (lv 0).boolGate (lv 1).boolGate with
  | none => have hb0' := hb0; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb0'; rw [hb0'] at h0; cases h0
  | some bz0 =>
  cases hb1 : pairCheckMul (vcPairAt bw 1) (vcPairAt omb 1) (lv 1).boolGate (lv 2).boolGate with
  | none => have hb1' := hb1; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb1'; rw [hb1'] at h1; cases h1
  | some bz1 =>
  cases hb2 : pairCheckMul (vcPairAt bw 2) (vcPairAt omb 2) (lv 2).boolGate (lv 0).boolGate with
  | none => have hb2' := hb2; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb2'; rw [hb2'] at h2; cases h2
  | some bz2 =>
    have hb0' := hb0; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb0'
    have hb1' := hb1; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb1'
    have hb2' := hb2; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb2'
    rw [hb0'] at h0; rw [hb1'] at h1; rw [hb2'] at h2
    dsimp only at h0 h1 h2
    let dw0 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x0 (cur i).x0
    let dw1 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x1 (cur i).x1
    let dw2 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x2 (cur i).x2
    let dw3 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x3 (cur i).x3
    let dw4 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x4 (cur i).x4
    let dw5 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x5 (cur i).x5
    cases s00 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw0 0) (lv 0).sel0 (lv 1).sel0 with
    | none => have u := s00; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u00 := s00; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u00; rw [u00] at h0
    cases s10 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw1 0) (lv 0).sel1 (lv 1).sel1 with
    | none => have u := s10; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u10 := s10; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u10; rw [u10] at h0
    cases s20 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw2 0) (lv 0).sel2 (lv 1).sel2 with
    | none => have u := s20; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u20 := s20; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u20; rw [u20] at h0
    cases s30 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw3 0) (lv 0).sel3 (lv 1).sel3 with
    | none => have u := s30; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u30 := s30; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u30; rw [u30] at h0
    cases s40 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw4 0) (lv 0).sel4 (lv 1).sel4 with
    | none => have u := s40; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u40 := s40; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u40; rw [u40] at h0
    cases s50 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw5 0) (lv 0).sel5 (lv 1).sel5 with
    | none => have u := s50; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u50 := s50; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u50; rw [u50] at h0
    cases s01 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw0 1) (lv 1).sel0 (lv 2).sel0 with
    | none => have u := s01; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u01 := s01; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u01; rw [u01] at h1
    cases s11 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw1 1) (lv 1).sel1 (lv 2).sel1 with
    | none => have u := s11; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u11 := s11; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u11; rw [u11] at h1
    cases s21 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw2 1) (lv 1).sel2 (lv 2).sel2 with
    | none => have u := s21; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u21 := s21; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u21; rw [u21] at h1
    cases s31 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw3 1) (lv 1).sel3 (lv 2).sel3 with
    | none => have u := s31; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u31 := s31; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u31; rw [u31] at h1
    cases s41 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw4 1) (lv 1).sel4 (lv 2).sel4 with
    | none => have u := s41; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u41 := s41; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u41; rw [u41] at h1
    cases s51 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw5 1) (lv 1).sel5 (lv 2).sel5 with
    | none => have u := s51; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u51 := s51; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u51; rw [u51] at h1
    cases s02 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw0 2) (lv 2).sel0 (lv 0).sel0 with
    | none => have u := s02; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u02 := s02; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u02; rw [u02] at h2
    cases s12 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw1 2) (lv 2).sel1 (lv 0).sel1 with
    | none => have u := s12; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u12 := s12; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u12; rw [u12] at h2
    cases s22 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw2 2) (lv 2).sel2 (lv 0).sel2 with
    | none => have u := s22; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u22 := s22; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u22; rw [u22] at h2
    cases s32 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw3 2) (lv 2).sel3 (lv 0).sel3 with
    | none => have u := s32; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u32 := s32; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u32; rw [u32] at h2
    cases s42 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw4 2) (lv 2).sel4 (lv 0).sel4 with
    | none => have u := s42; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u42 := s42; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u42; rw [u42] at h2
    cases s52 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw5 2) (lv 2).sel5 (lv 0).sel5 with
    | none => have u := s52; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
      have u52 := s52; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u52; rw [u52] at h2
      dsimp only at h0 h1 h2
      rw [(pairCheckMul_step (g := fun i => (lv i).boolGate) (e := 0) hb0).1] at h0
      rw [(pairCheckMul_step (g := fun i => (lv i).boolGate) (e := 1) hb1).1] at h1
      rw [(pairCheckMul_step (g := fun i => (lv i).boolGate) (e := 2) hb2).1] at h2
      rw [(pairCheckMul_step (g := fun i => (lv i).sel0) (e := 0) s00).1,
          (pairCheckMul_step (g := fun i => (lv i).sel1) (e := 0) s10).1,
          (pairCheckMul_step (g := fun i => (lv i).sel2) (e := 0) s20).1,
          (pairCheckMul_step (g := fun i => (lv i).sel3) (e := 0) s30).1,
          (pairCheckMul_step (g := fun i => (lv i).sel4) (e := 0) s40).1,
          (pairCheckMul_step (g := fun i => (lv i).sel5) (e := 0) s50).1] at h0
      rw [(pairCheckMul_step (g := fun i => (lv i).sel0) (e := 1) s01).1,
          (pairCheckMul_step (g := fun i => (lv i).sel1) (e := 1) s11).1,
          (pairCheckMul_step (g := fun i => (lv i).sel2) (e := 1) s21).1,
          (pairCheckMul_step (g := fun i => (lv i).sel3) (e := 1) s31).1,
          (pairCheckMul_step (g := fun i => (lv i).sel4) (e := 1) s41).1,
          (pairCheckMul_step (g := fun i => (lv i).sel5) (e := 1) s51).1] at h1
      rw [(pairCheckMul_step (g := fun i => (lv i).sel0) (e := 2) s02).1,
          (pairCheckMul_step (g := fun i => (lv i).sel1) (e := 2) s12).1,
          (pairCheckMul_step (g := fun i => (lv i).sel2) (e := 2) s22).1,
          (pairCheckMul_step (g := fun i => (lv i).sel3) (e := 2) s32).1,
          (pairCheckMul_step (g := fun i => (lv i).sel4) (e := 2) s42).1,
          (pairCheckMul_step (g := fun i => (lv i).sel5) (e := 2) s52).1] at h2
      dsimp only [vcPairAt, vcNextParty3] at h0 h1 h2
      let c0_3 : VcLane6_3 := fun i =>
        ⟨Goldilocks.add (cur i).x0 (lv i).sel0.out, Goldilocks.add (cur i).x1 (lv i).sel1.out,
         Goldilocks.add (cur i).x2 (lv i).sel2.out, Goldilocks.add (cur i).x3 (lv i).sel3.out,
         Goldilocks.add (cur i).x4 (lv i).sel4.out, Goldilocks.add (cur i).x5 (lv i).sel5.out⟩
      let c1_3 : VcLane6_3 := fun i =>
        ⟨Goldilocks.sub (lv i).sibShare.x0 (lv i).sel0.out, Goldilocks.sub (lv i).sibShare.x1 (lv i).sel1.out,
         Goldilocks.sub (lv i).sibShare.x2 (lv i).sel2.out, Goldilocks.sub (lv i).sibShare.x3 (lv i).sel3.out,
         Goldilocks.sub (lv i).sibShare.x4 (lv i).sel4.out, Goldilocks.sub (lv i).sibShare.x5 (lv i).sel5.out⟩
      let c2_3 : VcLane6_3 := fun i =>
        ⟨vcConstWire3 (vcSchemaLo epoch) i,
         vcConstWire3 (Goldilocks.ofNat layer) i,
         vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
         vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
         vcConstWire3 Goldilocks.one i,
         Goldilocks.zero⟩
      cases sp0 : pairCheckSponge3Perm 0 (lv 0).hashView (lv 1).hashView
          (vcPairAtLane6 c0_3 0) (vcPairAtLane6 c1_3 0) (vcPairAtLane6 c2_3 0) with
      | none => have sp0' := sp0; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp0'; rw [sp0'] at h0; cases h0
      | some u0 =>
      cases sp1 : pairCheckSponge3Perm 1 (lv 1).hashView (lv 2).hashView
          (vcPairAtLane6 c0_3 1) (vcPairAtLane6 c1_3 1) (vcPairAtLane6 c2_3 1) with
      | none => have sp1' := sp1; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp1'; rw [sp1'] at h1; cases h1
      | some u1 =>
      cases sp2 : pairCheckSponge3Perm 2 (lv 2).hashView (lv 0).hashView
          (vcPairAtLane6 c0_3 2) (vcPairAtLane6 c1_3 2) (vcPairAtLane6 c2_3 2) with
      | none => have sp2' := sp2; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp2'; rw [sp2'] at h2; cases h2
      | some u2 =>
        have sp0' := sp0; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp0'
        have sp1' := sp1; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp1'
        have sp2' := sp2; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp2'
        rw [sp0'] at h0; rw [sp1'] at h1; rw [sp2'] at h2
        dsimp only at h0 h1 h2
        obtain ⟨nextCur, hu0, hu1, hu2, hSpSum⟩ :=
          pairCheckSponge3Perm_extract3 (sv := fun i => (lv i).hashView) sp0 sp1 sp2
        rw [hu0] at h0; rw [hu1] at h1; rw [hu2] at h2
        injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
        refine ⟨nextCur, fun i => (lv i).boolGate.out, ho0.symm, ho1.symm, ho2.symm, ?_, ?_⟩
        · have hBz := pairCheckMul_extract3 (g := fun i => (lv i).boolGate) hb0 hb1 hb2
          rw [hBz]; congr 1; dsimp only [omb]; rw [vcSum3_sub, vcSum3_constWire]
        · rw [hSpSum]
          rw [vcMerkleStepArith.public_eq_1]
          rw [vcMerkleHashPair.public_eq_1]
          rw [vcMerkleChunks.public_eq_1]
          unfold lane6Add
          unfold lane6Sub
          unfold lane6Scale
          dsimp only
          congr 1
          simp only [vcSumLane6_3_eq]
          dsimp only [c0_3, c1_3, c2_3]
          simp only [vcSum3_add, vcSum3_sub, vcSum3_constWire, vcSum3_zero]
          rw [pairCheckMul_extract3 (g := fun i => (lv i).sel0) s00 s01 s02,
              pairCheckMul_extract3 (g := fun i => (lv i).sel1) s10 s11 s12,
              pairCheckMul_extract3 (g := fun i => (lv i).sel2) s20 s21 s22,
              pairCheckMul_extract3 (g := fun i => (lv i).sel3) s30 s31 s32,
              pairCheckMul_extract3 (g := fun i => (lv i).sel4) s40 s41 s42,
              pairCheckMul_extract3 (g := fun i => (lv i).sel5) s50 s51 s52]
          dsimp only [bw, dw0, dw1, dw2, dw3, dw4, dw5]
          simp only [vcSum3_sub]

def pairCheckMerklePath (e : Fin 3) (epoch : UInt64) :
    Nat → (Lane6 × Lane6) → List PartyMerkleLevelView → List PartyMerkleLevelView →
    Option ((Lane6 × Lane6) × List (Goldilocks × Goldilocks))
  | _, cur, [], [] => some (cur, [])
  | layer, cur, lvE :: restE, lvE1 :: restE1 =>
    match pairCheckMerkleLevel e epoch layer cur lvE lvE1 with
    | none => none
    | some (nextCur, bz) =>
      match pairCheckMerklePath e epoch (layer + 1) nextCur restE restE1 with
      | none => none
      | some (rootPair, bzs) => some (rootPair, bz :: bzs)
  | _, _, _, _ => none

def extractMerklePathCoins : (D : Nat) → List PartyMerkleLevelView → Option (Vec MerkleLevelCoins D)
  | 0, [] => some .nil
  | d + 1, lv :: rest =>
    match extractMerkleLevelCoins lv, extractMerklePathCoins d rest with
    | some hc, some tc => some (.cons hc tc)
    | _, _ => none
  | _, _ => none

def honestMerklePath3 (epoch : UInt64) :
    {D : Nat} → Nat → VcLane6_3 → Vec (VcWire3 × VcLane6_3) D → (Fin 3 → Vec MerkleLevelCoins D) →
    (Fin 3 → List PartyMerkleLevelView) × VcLane6_3 × List VcWire3
  | 0, _, cur, .nil, _ => (fun _ => [], cur, [])
  | _ + 1, layer, cur, .cons (b, sib) rest, mcs =>
    let step := honestMerkleLevel3 epoch layer cur b sib (fun i => (mcs i).head)
    let tail := honestMerklePath3 epoch (layer + 1) step.2.1 rest (fun i => (mcs i).tail)
    (fun i => step.1 i :: tail.1 i, tail.2.1, step.2.2 :: tail.2.2)

private theorem honestMerklePath3_length (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : VcLane6_3) (steps : Vec (VcWire3 × VcLane6_3) D)
      (mcs : Fin 3 → Vec MerkleLevelCoins D) (i : Fin 3),
      ((honestMerklePath3 epoch layer cur steps mcs).1 i).length = D
  | 0, _, _, .nil, _, _ => rfl
  | _ + 1, layer, cur, .cons (_, _) rest, mcs, i => by
    simp only [honestMerklePath3, List.length_cons]
    rw [honestMerklePath3_length epoch (layer + 1) _ rest (fun j => (mcs j).tail) i]

private theorem extractMerklePathCoins_honest (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : VcLane6_3) (steps : Vec (VcWire3 × VcLane6_3) D)
      (mcs : Fin 3 → Vec MerkleLevelCoins D) (i : Fin 3),
      extractMerklePathCoins D ((honestMerklePath3 epoch layer cur steps mcs).1 i) = some (mcs i)
  | 0, _, _, .nil, mcs, i => by cases mcs i; rfl
  | _ + 1, layer, cur, .cons (b, sib) rest, mcs, i => by
    simp only [honestMerklePath3, extractMerklePathCoins]
    rw [extractMerkleLevelCoins_honest,
        extractMerklePathCoins_honest epoch (layer + 1) _ rest (fun j => (mcs j).tail) i]
    dsimp only
    rw [Vec.eta_cons]

private theorem pairCheckMerklePath_honest (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : VcLane6_3) (steps : Vec (VcWire3 × VcLane6_3) D)
      (mcs : Fin 3 → Vec MerkleLevelCoins D) (e : Fin 3),
      pairCheckMerklePath e epoch layer (vcPairAtLane6 cur e)
        ((honestMerklePath3 epoch layer cur steps mcs).1 e)
        ((honestMerklePath3 epoch layer cur steps mcs).1 (vcNextParty3 e)) =
        some (vcPairAtLane6 (honestMerklePath3 epoch layer cur steps mcs).2.1 e,
              (honestMerklePath3 epoch layer cur steps mcs).2.2.map (fun w => vcPairAt w e))
  | 0, _, _, .nil, _, _ => rfl
  | _ + 1, layer, cur, .cons (b, sib) rest, mcs, e => by
    simp only [honestMerklePath3, pairCheckMerklePath, List.map]
    rw [pairCheckMerkleLevel_honest]; dsimp only
    rw [pairCheckMerklePath_honest epoch (layer + 1) _ rest (fun i => (mcs i).tail) e]

theorem pairCheckMerklePath_extract3 (epoch : UInt64) :
    ∀ (depth layer : Nat) (cur : VcLane6_3) (lvs : Fin 3 → List PartyMerkleLevelView)
      {o0 o1 o2 : (Lane6 × Lane6) × List (Goldilocks × Goldilocks)},
      (lvs 0).length = depth →
      pairCheckMerklePath 0 epoch layer (vcPairAtLane6 cur 0) (lvs 0) (lvs 1) = some o0 →
      pairCheckMerklePath 1 epoch layer (vcPairAtLane6 cur 1) (lvs 1) (lvs 2) = some o1 →
      pairCheckMerklePath 2 epoch layer (vcPairAtLane6 cur 2) (lvs 2) (lvs 0) = some o2 →
      ∃ (root3 : VcLane6_3) (bzs3 : List VcWire3) (steps : List (Goldilocks × Lane6)),
        steps.length = depth ∧
        o0 = (vcPairAtLane6 root3 0, bzs3.map (fun w => vcPairAt w 0)) ∧
        o1 = (vcPairAtLane6 root3 1, bzs3.map (fun w => vcPairAt w 1)) ∧
        o2 = (vcPairAtLane6 root3 2, bzs3.map (fun w => vcPairAt w 2)) ∧
        ((∀ z ∈ bzs3, vcSum3 z = Goldilocks.zero) →
          ∀ p ∈ steps, p.1 = Goldilocks.zero ∨ p.1 = Goldilocks.one) ∧
        vcSumLane6_3 root3 = evalVcMerklePathFrom epoch layer (vcSumLane6_3 cur) steps
  | 0, layer, cur, lvs, o0, o1, o2, hLen0, h0, h1, h2 => by
    cases hv0 : lvs 0 with
    | cons _ _ => rw [hv0] at hLen0; cases hLen0
    | nil =>
      cases hv1 : lvs 1 with
      | cons _ _ => rw [hv0, hv1] at h0; cases h0
      | nil =>
        cases hv2 : lvs 2 with
        | cons _ _ => rw [hv1, hv2] at h1; cases h1
        | nil =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckMerklePath] at h0 h1 h2
          injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
          exact ⟨cur, [], [], rfl, ho0.symm, ho1.symm, ho2.symm, (fun _ _ hp => nomatch hp), rfl⟩
  | depth + 1, layer, cur, lvs, o0, o1, o2, hLen0, h0, h1, h2 => by
    cases hv0 : lvs 0 with
    | nil => rw [hv0] at hLen0; cases hLen0
    | cons r0 rs0 =>
      rw [hv0] at hLen0; simp only [List.length_cons] at hLen0
      cases hv1 : lvs 1 with
      | nil => rw [hv0, hv1] at h0; cases h0
      | cons r1 rs1 =>
        cases hv2 : lvs 2 with
        | nil => rw [hv1, hv2] at h1; cases h1
        | cons r2 rs2 =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckMerklePath] at h0 h1 h2
          let lv : Fin 3 → PartyMerkleLevelView := fun | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2
          let rs : Fin 3 → List PartyMerkleLevelView := fun | ⟨0, _⟩ => rs0 | ⟨1, _⟩ => rs1 | ⟨2, _⟩ => rs2
          cases m0 : pairCheckMerkleLevel 0 epoch layer (vcPairAtLane6 cur 0) (lv 0) (lv 1) with
          | none => have m0' := m0; dsimp only [lv] at m0'; rw [m0'] at h0; cases h0
          | some p0 =>
          cases m1 : pairCheckMerkleLevel 1 epoch layer (vcPairAtLane6 cur 1) (lv 1) (lv 2) with
          | none => have m1' := m1; dsimp only [lv] at m1'; rw [m1'] at h1; cases h1
          | some p1 =>
          cases m2 : pairCheckMerkleLevel 2 epoch layer (vcPairAtLane6 cur 2) (lv 2) (lv 0) with
          | none => have m2' := m2; dsimp only [lv] at m2'; rw [m2'] at h2; cases h2
          | some p2 =>
            have m0' := m0; dsimp only [lv] at m0'
            have m1' := m1; dsimp only [lv] at m1'
            have m2' := m2; dsimp only [lv] at m2'
            rw [m0'] at h0; rw [m1'] at h1; rw [m2'] at h2
            obtain ⟨nextCur, bz, ep0, ep1, ep2, hBzEq, hNextEq⟩ := pairCheckMerkleLevel_extract3 m0 m1 m2
            rw [ep0] at h0; rw [ep1] at h1; rw [ep2] at h2
            dsimp only at h0 h1 h2
            cases t0 : pairCheckMerklePath 0 epoch (layer + 1) (vcPairAtLane6 nextCur 0) (rs 0) (rs 1) with
            | none => have t0' := t0; dsimp only [rs] at t0'; rw [t0'] at h0; cases h0
            | some q0 =>
            cases t1 : pairCheckMerklePath 1 epoch (layer + 1) (vcPairAtLane6 nextCur 1) (rs 1) (rs 2) with
            | none => have t1' := t1; dsimp only [rs] at t1'; rw [t1'] at h1; cases h1
            | some q1 =>
            cases t2 : pairCheckMerklePath 2 epoch (layer + 1) (vcPairAtLane6 nextCur 2) (rs 2) (rs 0) with
            | none => have t2' := t2; dsimp only [rs] at t2'; rw [t2'] at h2; cases h2
            | some q2 =>
              have t0' := t0; dsimp only [rs] at t0'
              have t1' := t1; dsimp only [rs] at t1'
              have t2' := t2; dsimp only [rs] at t2'
              rw [t0'] at h0; rw [t1'] at h1; rw [t2'] at h2
              obtain ⟨root3, bzs3, stepsRest, hSLen, eq0, eq1, eq2, hBoolRest, hRootSum⟩ :=
                pairCheckMerklePath_extract3 epoch depth (layer + 1) nextCur rs (by dsimp [rs]; omega) t0 t1 t2
              rw [eq0] at h0; rw [eq1] at h1; rw [eq2] at h2
              dsimp only at h0 h1 h2
              injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
              let bVal := vcSum3 (fun i => (lv i).bitShare)
              let sibVal := vcSumLane6_3 (fun i => (lv i).sibShare)
              refine ⟨root3, bz :: bzs3, (bVal, sibVal) :: stepsRest,
                by simp [hSLen], ho0.symm, ho1.symm, ho2.symm, ?_, ?_⟩
              · intro hAllZ p hp
                rcases List.mem_cons.mp hp with rfl | hpRest
                · have h0Bz : vcSum3 bz = Goldilocks.zero := hAllZ bz (.head bzs3)
                  rw [hBzEq] at h0Bz
                  exact goldilocks_bool_gate_zero_or_one bVal h0Bz
                · exact hBoolRest (fun z hz => hAllZ z (.tail bz hz)) p hpRest
              · dsimp only [evalVcMerklePathFrom]
                rw [← hNextEq]
                exact hRootSum

theorem Vec.toList_nil {α : Type} : (Vec.nil : Vec α 0).toList = [] := by rfl

theorem Vec.toList_cons {α : Type} {n : Nat} (x : α) (xs : Vec α n) :
    (Vec.cons x xs).toList = x :: xs.toList := by rfl

#export_eqns Vec.replicate

#export_eqns vcSum3

/-- Self-inverse field subtraction bijection `x ↦ K - x` (`0 Classical.choice`). -/
def goldSubFromConstEquiv (K : Goldilocks) : SimpleEquiv Goldilocks Goldilocks where
  toFun x := Goldilocks.sub K x
  invFun y := Goldilocks.sub K y
  left_inv x := by
    rw [← goldOfInt_nat K, ← goldOfInt_nat x]
    simp only [goldOfInt_sub]; congr 1; omega
  right_inv y := by
    rw [← goldOfInt_nat K, ← goldOfInt_nat y]
    simp only [goldOfInt_sub]; congr 1; omega


/-! #### Gate-by-Gate Full-Circuit Simulator & `SimpleEquiv` Coin-to-Output Bijections -/

/-- Simulator step for one ZKBoo multiplication gate (ZERO secret witness inputs!). -/
def simMulGate (px py : Goldilocks × Goldilocks) (rE rE1 simOutE1 : Goldilocks) :
    (PartyMulView × PartyMulView) × (Goldilocks × Goldilocks) :=
  let outE := vcMulExpectedPair px.1 px.2 py.1 py.2 rE rE1
  (({ r := rE, out := outE }, { r := rE1, out := simOutE1 }), (outE, simOutE1))

/-- Bijection mapping unopened coin `rU` to party `(e+1)%3`'s multiplication output share `out_{e+1}`. -/
def mulGateOutEquiv (e : Fin 3) (wx wy : VcWire3) (rE1 : Goldilocks) :
    SimpleEquiv Goldilocks Goldilocks :=
  let e1 := vcNextParty3 e
  let e2 := vcUnopenedParty3 e
  let crossE1 := Goldilocks.add (Goldilocks.mul (wx e1) (wy e1))
    (Goldilocks.add (Goldilocks.mul (wx e1) (wy e2)) (Goldilocks.mul (wx e2) (wy e1)))
  goldSubFromConstEquiv (Goldilocks.add crossE1 rE1)

private theorem simMulGate_eq_honest (e : Fin 3) (wx wy : VcWire3) (rE rE1 rU : Goldilocks) :
    let r := mkParty3At e rE rE1 rU
    simMulGate (vcPairAt wx e) (vcPairAt wy e) rE rE1 ((mulGateOutEquiv e wx wy rE1).toFun rU) =
      ((honestMulView3 wx wy r e, honestMulView3 wx wy r (vcNextParty3 e)),
       vcPairAt (vcMulGate3 wx wy r) e) := by
  unfold simMulGate mulGateOutEquiv goldSubFromConstEquiv honestMulView3 vcMulGate3 vcPairAt vcMulExpectedPair
  dsimp only
  rw [mkParty3At_e, mkParty3At_next, vcNextParty3_next_eq_unopened, mkParty3At_unopened]

private theorem pairCheckMul_sim (px py : Goldilocks × Goldilocks) (rE rE1 simOutE1 : Goldilocks) :
    pairCheckMul px py (simMulGate px py rE rE1 simOutE1).1.1
      (simMulGate px py rE rE1 simOutE1).1.2 =
      some (simMulGate px py rE rE1 simOutE1).2 := by
  unfold pairCheckMul simMulGate
  dsimp only
  simp only [↓reduceIte]

/-- Simulator step for one S-box (`x ↦ x^7`, 4 multiplication gates, ZERO secret witness inputs!). -/
def simSbox (px : Goldilocks × Goldilocks) (scE scE1 simOutE1 : SboxCoins) :
    (PartySboxView × PartySboxView) × (Goldilocks × Goldilocks) :=
  let m1 := simMulGate px px scE.1 scE1.1 simOutE1.1
  let m2 := simMulGate m1.2 px scE.2.1 scE1.2.1 simOutE1.2.1
  let m3 := simMulGate m1.2 m1.2 scE.2.2.1 scE1.2.2.1 simOutE1.2.2.1
  let m4 := simMulGate m3.2 m2.2 scE.2.2.2 scE1.2.2.2 simOutE1.2.2.2
  ((⟨m1.1.1, m2.1.1, m3.1.1, m4.1.1⟩, ⟨m1.1.2, m2.1.2, m3.1.2, m4.1.2⟩), m4.2)


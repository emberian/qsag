module
public import Qsag.Math.Algebra
public import Qsag.Tactic.Prelude
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Wiedemann Tower Coordinates & `LawfulCommRing` Algebra -/

/-- Coordinates in the Wiedemann binary tower $X^2 + x_k X + 1 = 0$. -/
@[expose] def TowerElem : Nat → Type
  | 0 => Bool
  | k + 1 => TowerElem k × TowerElem k

abbrev Tower8 := TowerElem 3
abbrev Tower128 := TowerElem 7
abbrev Tower256 := TowerElem 8
abbrev TowerBitVec (k : Nat) := BitVec (2 ^ k)
abbrev Tower128Exec := BitVec 128
abbrev Tower256Exec := BitVec 256

@[expose] def towerZero : (k : Nat) → TowerElem k
  | 0 => false
  | k + 1 => (towerZero k, towerZero k)

@[expose] def towerOne : (k : Nat) → TowerElem k
  | 0 => true
  | k + 1 => (towerOne k, towerZero k)

@[expose] def towerX : (k : Nat) → TowerElem k
  | 0 => true
  | k + 1 => (towerZero k, towerOne k)

@[expose] def towerAdd : (k : Nat) → TowerElem k → TowerElem k → TowerElem k
  | 0, a, b => a ^^ b
  | k + 1, a, b => (towerAdd k a.1 b.1, towerAdd k a.2 b.2)

@[expose] def towerMul : (k : Nat) → TowerElem k → TowerElem k → TowerElem k
  | 0, a, b => a && b
  | k + 1, a, b =>
    (towerAdd k (towerMul k a.1 b.1) (towerMul k a.2 b.2),
     towerAdd k (towerAdd k (towerMul k a.1 b.2) (towerMul k a.2 b.1))
       (towerMul k (towerX k) (towerMul k a.2 b.2)))

@[expose] def towerScaleX : (k : Nat) → TowerElem k → TowerElem k
  | 0, a => a
  | k + 1, a => (a.2, towerAdd k a.1 (towerScaleX k a.2))

instance towerDecidableEq : (k : Nat) → DecidableEq (TowerElem k)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | k + 1 => @instDecidableEqProd _ _ (towerDecidableEq k) (towerDecidableEq k)

instance towerInhabited (k : Nat) : Inhabited (TowerElem k) := ⟨towerZero k⟩

@[simp] theorem towerAdd_self_zero (k : Nat) (a : TowerElem k) :
    towerAdd k a a = towerZero k := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => exact Prod.ext (ih a.1) (ih a.2)

theorem towerAdd_comm (k : Nat) (a b : TowerElem k) :
    towerAdd k a b = towerAdd k b a := by
  induction k with
  | zero => cases a <;> cases b <;> rfl
  | succ k ih => exact Prod.ext (ih a.1 b.1) (ih a.2 b.2)

theorem towerAdd_assoc (k : Nat) (a b c : TowerElem k) :
    towerAdd k (towerAdd k a b) c = towerAdd k a (towerAdd k b c) := by
  induction k with
  | zero => cases a <;> cases b <;> cases c <;> rfl
  | succ k ih => exact Prod.ext (ih a.1 b.1 c.1) (ih a.2 b.2 c.2)

@[simp] theorem towerAdd_zero (k : Nat) (a : TowerElem k) :
    towerAdd k a (towerZero k) = a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => exact Prod.ext (ih a.1) (ih a.2)

@[simp] theorem towerZero_add (k : Nat) (a : TowerElem k) :
    towerAdd k (towerZero k) a = a := by rw [towerAdd_comm, towerAdd_zero]

theorem towerAdd_left_comm (k : Nat) (a b c : TowerElem k) :
    towerAdd k a (towerAdd k b c) = towerAdd k b (towerAdd k a c) := by
  rw [← towerAdd_assoc, towerAdd_comm k a b, towerAdd_assoc]

@[simp] theorem towerAdd_cancel (k : Nat) (a b : TowerElem k) :
    towerAdd k a (towerAdd k a b) = b := by
  rw [← towerAdd_assoc, towerAdd_self_zero, towerZero_add]

@[simp] theorem towerMul_zero (k : Nat) (a : TowerElem k) :
    towerMul k a (towerZero k) = towerZero k := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => simp only [towerMul, towerZero, ih, towerAdd_self_zero]; rfl

theorem towerMul_comm (k : Nat) (a b : TowerElem k) :
    towerMul k a b = towerMul k b a := by
  induction k with
  | zero => cases a <;> cases b <;> rfl
  | succ k ih =>
    simp only [towerMul]
    rw [ih a.1 b.1, ih a.2 b.2, ih a.1 b.2, ih a.2 b.1,
      towerAdd_comm k (towerMul k b.2 a.1) (towerMul k b.1 a.2)]

@[simp] theorem towerZero_mul (k : Nat) (a : TowerElem k) :
    towerMul k (towerZero k) a = towerZero k := by rw [towerMul_comm, towerMul_zero]

@[simp] theorem towerMul_one (k : Nat) (a : TowerElem k) :
    towerMul k a (towerOne k) = a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => cases a; simp [towerMul, towerOne, ih]; rfl

@[simp] theorem towerOne_mul (k : Nat) (a : TowerElem k) :
    towerMul k (towerOne k) a = a := by rw [towerMul_comm, towerMul_one]

theorem towerMul_add_distrib (k : Nat) (a b c : TowerElem k) :
    towerMul k a (towerAdd k b c) =
      towerAdd k (towerMul k a b) (towerMul k a c) := by
  induction k with
  | zero => cases a <;> cases b <;> cases c <;> rfl
  | succ k ih =>
    simp only [towerMul, towerAdd, ih]
    congr 1 <;> simp only [towerAdd_assoc, towerAdd_left_comm]

theorem towerAdd_mul_distrib (k : Nat) (a b c : TowerElem k) :
    towerMul k (towerAdd k a b) c =
      towerAdd k (towerMul k a c) (towerMul k b c) := by
  rw [towerMul_comm, towerMul_add_distrib, towerMul_comm k c a, towerMul_comm k c b]

theorem towerMul_left_comm_of_assoc (k : Nat)
    (ha : ∀ a b c, towerMul k (towerMul k a b) c = towerMul k a (towerMul k b c))
    (a b c : TowerElem k) :
    towerMul k a (towerMul k b c) = towerMul k b (towerMul k a c) := by
  rw [← ha, towerMul_comm k a b, ha]

theorem towerMul_assoc (k : Nat) (a b c : TowerElem k) :
    towerMul k (towerMul k a b) c = towerMul k a (towerMul k b c) := by
  induction k with
  | zero => cases a <;> cases b <;> cases c <;> rfl
  | succ k ih =>
    simp only [towerMul, towerMul_add_distrib, towerAdd_mul_distrib]
    congr 1 <;>
      simp only [ih, towerMul_comm k, towerMul_left_comm_of_assoc k ih,
        towerAdd_assoc, towerAdd_comm, towerAdd_left_comm]

theorem towerScaleX_eq_mul (k : Nat) (a : TowerElem k) :
    towerScaleX k a = towerMul k (towerX k) a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => simp [towerScaleX, towerX, towerMul, ih] <;> rfl

/-- Structural 3-multiply Karatsuba over `TowerElem k`. -/
def towerKaratsuba : (k : Nat) → TowerElem k → TowerElem k → TowerElem k
  | 0, a, b => a && b
  | k + 1, a, b =>
    let p := towerKaratsuba k a.1 b.1
    let q := towerKaratsuba k a.2 b.2
    let r := towerKaratsuba k (towerAdd k a.1 a.2) (towerAdd k b.1 b.2)
    (towerAdd k p q, towerAdd k (towerAdd k r (towerAdd k p q)) (towerScaleX k q))

theorem towerKaratsuba_eq (k : Nat) (a b : TowerElem k) :
    towerKaratsuba k a b = towerMul k a b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [towerKaratsuba, ih, towerMul, towerMul_add_distrib,
      towerAdd_mul_distrib, towerScaleX_eq_mul]
    congr 1
    simp only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm,
      towerAdd_self_zero, towerAdd_zero, towerAdd_cancel]

@[csimp] theorem towerMul_eq_karatsuba : towerMul = towerKaratsuba := by
  funext k a b
  exact (towerKaratsuba_eq k a b).symm

/-- Subfield embedding $\mathcal{T}_k \hookrightarrow \mathcal{T}_{k+1}$. -/
@[expose] def embedTower (k : Nat) (a : TowerElem k) : TowerElem (k + 1) := (a, towerZero k)

theorem embedTower_zero (k : Nat) : embedTower k (towerZero k) = towerZero (k + 1) := rfl
theorem embedTower_one (k : Nat) : embedTower k (towerOne k) = towerOne (k + 1) := rfl

theorem embedTower_add (k : Nat) (a b : TowerElem k) :
    embedTower k (towerAdd k a b) = towerAdd (k + 1) (embedTower k a) (embedTower k b) := by
  simp [embedTower, towerAdd] <;> rfl

theorem embedTower_mul (k : Nat) (a b : TowerElem k) :
    embedTower k (towerMul k a b) = towerMul (k + 1) (embedTower k a) (embedTower k b) := by
  simp [embedTower, towerMul] <;> rfl

theorem embedTower_injective (k : Nat) (a b : TowerElem k)
    (h : embedTower k a = embedTower k b) : a = b := congrArg Prod.fst h

def embedTowerChain (k : Nat) : (d : Nat) → TowerElem k → TowerElem (k + d)
  | 0, a => a
  | d + 1, a => embedTower (k + d) (embedTowerChain k d a)

theorem embedTowerChain_injective (k d : Nat) (a b : TowerElem k)
    (h : embedTowerChain k d a = embedTowerChain k d b) : a = b := by
  induction d with
  | zero => exact h
  | succ d ih => exact ih (embedTower_injective _ _ _ h)

instance towerCommRingOps (k : Nat) : CommRingOps (TowerElem k) where
  zero := towerZero k
  one := towerOne k
  add := towerAdd k
  mul := towerMul k
  neg := id
  sub := towerAdd k

instance towerRing (k : Nat) : LawfulCommRing (TowerElem k) where
  add_assoc := towerAdd_assoc k
  add_comm := towerAdd_comm k
  zero_add := towerZero_add k
  add_zero := towerAdd_zero k
  add_left_neg := towerAdd_self_zero k
  sub_eq_add_neg _ _ := rfl
  mul_assoc := towerMul_assoc k
  mul_comm := towerMul_comm k
  one_mul := towerOne_mul k
  mul_one := towerMul_one k
  left_distrib := towerMul_add_distrib k
  right_distrib := towerAdd_mul_distrib k

/-! ## 2. Packed `BitVec (2^k)` `Spec ↔ Exec` Refinement (`Simulates`) -/

def joinBits (k : Nat) (lo hi : TowerBitVec k) : TowerBitVec (k + 1) :=
  (hi ++ lo).cast (by simp [Nat.pow_succ, Nat.mul_two])

def lowBits (k : Nat) (a : TowerBitVec (k + 1)) : TowerBitVec k := a.extractLsb' 0 (2 ^ k)
def highBits (k : Nat) (a : TowerBitVec (k + 1)) : TowerBitVec k := a.extractLsb' (2 ^ k) (2 ^ k)

@[simp] theorem lowBits_join (k : Nat) (lo hi : TowerBitVec k) :
    lowBits k (joinBits k lo hi) = lo := by
  simp [lowBits, joinBits, BitVec.extractLsb'_cast, BitVec.extractLsb'_append_eq_right]

@[simp] theorem highBits_join (k : Nat) (lo hi : TowerBitVec k) :
    highBits k (joinBits k lo hi) = hi := by
  simp [highBits, joinBits, BitVec.extractLsb'_cast, BitVec.extractLsb'_append_eq_left]

@[simp] theorem joinBits_split (k : Nat) (a : TowerBitVec (k + 1)) :
    joinBits k (lowBits k a) (highBits k a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [joinBits, lowBits, highBits, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  split <;> simp_all [Nat.pow_succ, Nat.mul_two] <;> omega

theorem joinBits_xor (k : Nat) (a b c d : TowerBitVec k) :
    joinBits k (a ^^^ b) (c ^^^ d) = joinBits k a c ^^^ joinBits k b d := by
  simp [joinBits, BitVec.xor_append]

@[expose] def packTower : (k : Nat) → TowerElem k → TowerBitVec k
  | 0, a => BitVec.ofBool a
  | k + 1, a => joinBits k (packTower k a.1) (packTower k a.2)

@[expose] def unpackTower : (k : Nat) → TowerBitVec k → TowerElem k
  | 0, a => a.getLsbD 0
  | k + 1, a => (unpackTower k (lowBits k a), unpackTower k (highBits k a))

@[simp] theorem packTower_zero (k : Nat) : packTower k (towerZero k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [packTower, towerZero, ih, joinBits]

@[simp] theorem unpackTower_packTower (k : Nat) (a : TowerElem k) :
    unpackTower k (packTower k a) = a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih =>
    cases a
    simp only [packTower, unpackTower, lowBits_join, highBits_join, ih]; rfl

@[simp] theorem unpackTower_zero (k : Nat) : unpackTower k 0 = towerZero k := by
  rw [← packTower_zero k, unpackTower_packTower]

@[simp] theorem packTower_unpackTower (k : Nat) (a : TowerBitVec k) :
    packTower k (unpackTower k a) = a := by
  induction k with
  | zero =>
    exact (BitVec.setWidth_one (x := a)).symm.trans (BitVec.setWidth_eq _)
  | succ k ih => simp only [packTower, unpackTower, ih, joinBits_split]

theorem packTower_injective (k : Nat) (a b : TowerElem k)
    (h : packTower k a = packTower k b) : a = b := by
  have := congrArg (unpackTower k) h
  simpa only [unpackTower_packTower] using this

theorem packTower_add (k : Nat) (a b : TowerElem k) :
    packTower k (towerAdd k a b) = packTower k a ^^^ packTower k b := by
  induction k with
  | zero => exact BitVec.ofBool_xor_ofBool.symm
  | succ k ih => simp only [packTower, towerAdd, ih, joinBits_xor]

def scaleXExec : (k : Nat) → TowerBitVec k → TowerBitVec k
  | 0, a => a
  | k + 1, a => joinBits k (highBits k a) (lowBits k a ^^^ scaleXExec k (highBits k a))

def mulExec : (k : Nat) → TowerBitVec k → TowerBitVec k → TowerBitVec k
  | 0, a, b => a &&& b
  | k + 1, a, b =>
    let al := lowBits k a; let ah := highBits k a
    let bl := lowBits k b; let bh := highBits k b
    let p := mulExec k al bl
    let q := mulExec k ah bh
    let r := mulExec k (al ^^^ ah) (bl ^^^ bh)
    joinBits k (p ^^^ q) (r ^^^ (p ^^^ q) ^^^ scaleXExec k q)

theorem scaleXExec_refines (k : Nat) (a : TowerElem k) :
    scaleXExec k (packTower k a) = packTower k (towerScaleX k a) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [scaleXExec, packTower, lowBits_join, highBits_join,
      ih, towerScaleX, packTower_add]

theorem mulExec_refines (k : Nat) (a b : TowerElem k) :
    mulExec k (packTower k a) (packTower k b) = packTower k (towerMul k a b) := by
  induction k with
  | zero => exact BitVec.ofBool_and_ofBool
  | succ k ih =>
    rw [← towerKaratsuba_eq]
    simp only [mulExec, packTower, lowBits_join, highBits_join, ← packTower_add,
      ih, scaleXExec_refines, towerKaratsuba, towerKaratsuba_eq]

def Simulates (k : Nat) (spec : TowerElem k) (exec : TowerBitVec k) : Prop :=
  packTower k spec = exec

theorem Simulates.add (k : Nat) {a b : TowerElem k} {x y : TowerBitVec k}
    (ha : Simulates k a x) (hb : Simulates k b y) :
    Simulates k (towerAdd k a b) (x ^^^ y) := by
  unfold Simulates at *
  rw [packTower_add, ha, hb]

theorem Simulates.mul (k : Nat) {a b : TowerElem k} {x y : TowerBitVec k}
    (ha : Simulates k a x) (hb : Simulates k b y) :
    Simulates k (towerMul k a b) (mulExec k x y) := by
  unfold Simulates at *
  rw [← ha, ← hb, mulExec_refines]

/-! ## 3. Artin–Schreier Trace Irreducibility, Norm Inversion & `NoZeroDivisors` -/

def towerTrace : (k : Nat) → TowerElem k → Bool
  | 0, a => a
  | k + 1, a => towerTrace k (towerMul k (towerX k) a.2)

@[simp] theorem towerTrace_zero (k : Nat) : towerTrace k (towerZero k) = false := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [towerTrace, towerZero, towerMul_zero] using ih

theorem towerTrace_add (k : Nat) (a b : TowerElem k) :
    towerTrace k (towerAdd k a b) = (towerTrace k a ^^ towerTrace k b) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [towerTrace, towerAdd, towerMul_add_distrib, ih]

@[simp] theorem towerTrace_X (k : Nat) : towerTrace k (towerX k) = true := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [towerTrace, towerX, towerMul_one] using ih

theorem towerTrace_square (k : Nat) (a : TowerElem k) :
    towerTrace k (towerMul k a a) = towerTrace k a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih =>
    simp only [towerTrace, towerMul]
    rw [towerMul_comm k a.2 a.1, towerAdd_self_zero, towerZero_add]
    have h : towerMul k (towerX k) (towerMul k (towerX k) (towerMul k a.2 a.2)) =
        towerMul k (towerMul k (towerX k) a.2) (towerMul k (towerX k) a.2) := by
      simp only [towerMul_assoc, towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
    rw [h, ih]

def towerInvX : (k : Nat) → TowerElem k
  | 0 => true
  | k + 1 => (towerX k, towerOne k)

@[simp] theorem towerX_mul_invX (k : Nat) :
    towerMul k (towerX k) (towerInvX k) = towerOne k := by
  cases k with
  | zero => rfl
  | succ k => simp [towerMul, towerX, towerInvX, towerOne]; rfl

@[simp] theorem towerTrace_invX (k : Nat) : towerTrace k (towerInvX k) = true := by
  cases k with
  | zero => rfl
  | succ k => simp only [towerTrace, towerInvX, towerMul_one, towerTrace_X]

theorem towerOne_ne_zero (k : Nat) : towerOne k ≠ towerZero k := by
  induction k with
  | zero => decide
  | succ k ih => exact fun h => ih (congrArg Prod.fst h)

/-- Irreducibility of $X^2 + x_k X + 1$ over $\mathcal{T}_k$ at every level $k$. -/
theorem tower_quadratic_no_root (k : Nat) (z : TowerElem k) :
    towerAdd k (towerAdd k (towerMul k z z) (towerMul k (towerX k) z)) (towerOne k) ≠
      towerZero k := by
  intro hz
  let u := towerInvX k
  let v := towerMul k z u
  have hi : towerMul k (towerX k) u = towerOne k := towerX_mul_invX k
  have he := congrArg (towerMul k (towerMul k u u)) hz
  rw [towerMul_add_distrib, towerMul_add_distrib, towerMul_one, towerMul_zero] at he
  have hsq : towerMul k (towerMul k u u) (towerMul k z z) = towerMul k v v := by
    dsimp [v]
    simp only [towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
  have hx : towerMul k (towerMul k u u) (towerMul k (towerX k) z) = v := by
    calc
      _ = towerMul k (towerMul k (towerX k) u) (towerMul k z u) := by
        simp only [towerMul_assoc, towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
      _ = v := by rw [hi, towerOne_mul]
  rw [hsq, hx] at he
  have ht := congrArg (towerTrace k) he
  rw [towerTrace_add, towerTrace_add, towerTrace_square, towerTrace_square,
    towerTrace_zero] at ht
  have hu : towerTrace k u = true := towerTrace_invX k
  rw [hu, Bool.xor_self] at ht
  contradiction

def towerNorm (k : Nat) (a : TowerElem (k + 1)) : TowerElem k :=
  towerAdd k (towerAdd k (towerMul k a.1 a.1)
    (towerMul k (towerX k) (towerMul k a.1 a.2))) (towerMul k a.2 a.2)

/-- Recursive quadratic-norm field inversion in $\mathcal{T}_k$ (`towerInv k 0 = 0`). -/
def towerInv : (k : Nat) → TowerElem k → TowerElem k
  | 0, a => a
  | k + 1, a =>
    let ni := towerInv k (towerNorm k a)
    (towerMul k (towerAdd k a.1 (towerMul k (towerX k) a.2)) ni,
     towerMul k a.2 ni)

theorem towerNorm_ne_zero (k : Nat)
    (hi : ∀ a : TowerElem k, a ≠ towerZero k → towerMul k a (towerInv k a) = towerOne k)
    (a : TowerElem (k + 1)) (ha : a ≠ towerZero (k + 1)) :
    towerNorm k a ≠ towerZero k := by
  intro hn
  by_cases hb : a.2 = towerZero k
  · have h0 : a.1 ≠ towerZero k := fun h0 => ha (Prod.ext h0 hb)
    have hsq : towerMul k a.1 a.1 = towerZero k := by simpa [towerNorm, hb] using hn
    have he := congrArg (towerMul k (towerInv k a.1)) hsq
    rw [← towerMul_assoc, towerMul_comm k (towerInv k a.1), hi a.1 h0,
      towerOne_mul, towerMul_zero] at he
    exact h0 he
  · let b := towerInv k a.2
    have hiB : towerMul k a.2 b = towerOne k := hi a.2 hb
    let z := towerMul k a.1 b
    have he := congrArg (towerMul k (towerMul k b b)) hn
    simp only [towerNorm, towerMul_add_distrib, towerMul_zero] at he
    have h1 : towerMul k (towerMul k b b) (towerMul k a.1 a.1) = towerMul k z z := by
      dsimp [z]
      simp only [towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
    have h2 : towerMul k (towerMul k b b)
        (towerMul k (towerX k) (towerMul k a.1 a.2)) = towerMul k (towerX k) z := by
      calc
        _ = towerMul k (towerMul k a.2 b) (towerMul k (towerX k) z) := by
          dsimp [z]
          simp only [towerMul_assoc, towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
        _ = _ := by rw [hiB, towerOne_mul]
    have h3 : towerMul k (towerMul k b b) (towerMul k a.2 a.2) = towerOne k := by
      calc
        _ = towerMul k (towerMul k a.2 b) (towerMul k a.2 b) := by
          simp only [towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]
        _ = _ := by rw [hiB, towerOne_mul]
    rw [h1, h2, h3] at he
    exact tower_quadratic_no_root k z he

theorem towerMul_inv (k : Nat) (a : TowerElem k) (ha : a ≠ towerZero k) :
    towerMul k a (towerInv k a) = towerOne k := by
  induction k with
  | zero => cases a <;> simp_all [towerZero, towerMul, towerInv, towerOne] <;> rfl
  | succ k ih =>
    have hn := towerNorm_ne_zero k ih a ha
    have hni := ih (towerNorm k a) hn
    simp only [towerInv, towerMul, towerMul_add_distrib, towerAdd_mul_distrib]
    apply Prod.ext
    · change _ = towerOne k
      rw [← hni]
      simp only [towerNorm, towerAdd_mul_distrib, towerMul_assoc,
        towerMul_comm, towerAdd_comm, towerAdd_left_comm]
    · change _ = towerZero k
      simp only [towerMul_assoc, towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k),
        towerAdd_self_zero, towerAdd_cancel]

theorem towerMul_eq_zero_iff (k : Nat) (a b : TowerElem k) :
    towerMul k a b = towerZero k ↔ a = towerZero k ∨ b = towerZero k := by
  constructor
  · intro h
    if ha : a = towerZero k then exact Or.inl ha
    else
      right
      have he := congrArg (towerMul k (towerInv k a)) h
      rw [← towerMul_assoc, towerMul_comm k (towerInv k a), towerMul_inv k a ha,
        towerOne_mul, towerMul_zero] at he
      exact he
  · rintro (rfl | rfl) <;> simp

instance towerNoZeroDivisors (k : Nat) : NoZeroDivisors (TowerElem k) where
  eq_zero_or_eq_zero_of_mul_eq_zero h := (towerMul_eq_zero_iff k _ _).mp h

theorem towerMul_cancel_left (k : Nat) (a b c : TowerElem k)
    (ha : a ≠ towerZero k) (h : towerMul k a b = towerMul k a c) : b = c := by
  have he := congrArg (towerMul k (towerInv k a)) h
  simpa only [← towerMul_assoc, towerMul_comm k (towerInv k a) a,
    towerMul_inv k a ha, towerOne_mul] using he

/-! ## 4. Polynomial Authentication & `Tower128` Root Counting -/

def ghashPoly (H : Tower128) (blocks : List Tower128) : Tower128 :=
  RoundPoly.evalCoeffs (towerZero 7 :: blocks.reverse) H

theorem ghashDiff_roots_bound (bs₁ bs₂ : List Tower128) (L : Nat) (keys : List Tower128)
    (h₁ : bs₁.length ≤ L) (h₂ : bs₂.length ≤ L) (hnd : keys.Nodup)
    (hne : ∃ H, ghashPoly H bs₁ ≠ ghashPoly H bs₂)
    (heq : ∀ H ∈ keys, ghashPoly H bs₁ = ghashPoly H bs₂) : keys.length ≤ L := by
  let cs := RoundPoly.subCoeffs (towerZero 7 :: bs₁.reverse) (towerZero 7 :: bs₂.reverse)
  have hlen : cs.length ≤ L + 1 := by
    simp only [cs, RoundPoly.subCoeffs_length, List.length_cons, List.length_reverse]
    exact Nat.max_le.mpr ⟨Nat.succ_le_succ h₁, Nat.succ_le_succ h₂⟩
  have hev (H : Tower128) : RoundPoly.evalCoeffs cs H =
      towerAdd 7 (ghashPoly H bs₁) (ghashPoly H bs₂) :=
    RoundPoly.evalCoeffs_sub _ _ H
  have hnz : ∃ H, RoundPoly.evalCoeffs cs H ≠ towerZero 7 := by
    obtain ⟨H, hH⟩ := hne
    refine ⟨H, ?_⟩
    rw [hev]
    intro h
    have := congrArg (towerAdd 7 (ghashPoly H bs₁)) h
    rw [towerAdd_cancel, towerAdd_zero] at this
    exact hH this.symm
  have hb := RoundPoly.roots_nodup_length_le L cs keys hnd hlen hnz
  have hf : keys.filter (fun H => decide (RoundPoly.evalCoeffs cs H = towerZero 7)) = keys := by
    apply List.filter_eq_self.mpr
    intro H hH
    simp only [hev, heq H hH, towerAdd_self_zero, decide_true]
  change (keys.filter (fun H => decide (RoundPoly.evalCoeffs cs H = towerZero 7))).length ≤ L at hb
  rw [hf] at hb
  exact hb

def packTowerLenBlock (aadBits ctBits : UInt64) : Tower128 :=
  unpackTower 7 (joinBits 6 ctBits.toBitVec aadBits.toBitVec)

theorem packTowerLenBlock_injective {a₁ c₁ a₂ c₂ : UInt64}
    (h : packTowerLenBlock a₁ c₁ = packTowerLenBlock a₂ c₂) : a₁ = a₂ ∧ c₁ = c₂ := by
  have hp := congrArg (packTower 7) h
  simp only [packTowerLenBlock, packTower_unpackTower] at hp
  have hLo := congrArg (lowBits 6) hp
  have hHi := congrArg (highBits 6) hp
  simp only [lowBits_join, highBits_join] at hLo hHi
  exact ⟨UInt64.eq_of_toBitVec_eq hHi, UInt64.eq_of_toBitVec_eq hLo⟩

end Qsag

namespace Qsag
set_option autoImplicit false
namespace MigrationExecution

/-- Rust's little-endian polynomial coefficients, not `packTower 7`. -/
abbrev RustGf128 := BitVec 128

/-- Multiplication by x modulo x^128 + x^7 + x^2 + x + 1. -/
def rustGf128MulX (a : RustGf128) : RustGf128 :=
  (a <<< 1) ^^^ (if a.getLsbD 127 then 0x87#128 else 0#128)

/-- The 128 iterations of `qsag_asm::gf2_128_mul_portable`, with its accumulator
    explicit. The branch denotes Rust's all-zero/all-one selection mask. -/
def rustGf128MulLoop : Nat → RustGf128 → RustGf128 → RustGf128 → RustGf128
  | 0, _, _, acc => acc
  | n + 1, x, y, acc =>
    rustGf128MulLoop n (rustGf128MulX x) (y >>> 1)
      (acc ^^^ (if y.getLsbD 0 then x else 0#128))

def rustGf128Mul (a b : RustGf128) : RustGf128 :=
  rustGf128MulLoop 128 a b 0#128

/-- `[low, high]` in Rust has exactly this coefficient order. -/
def rustGf128OfLimbs (lo hi : UInt64) : RustGf128 :=
  BitVec.ofNat 128 (lo.toNat + 2^64 * hi.toNat)


/-- Transparent Wiedemann coordinate bit-packing (`TowerElem k ≃ BitVec (2^k)`) free of `BitVec.cast`. -/
def wiedemannToNat : (k : Nat) → TowerElem k → Nat
  | 0, a => match a with | true => 1 | false => 0
  | k + 1, a => wiedemannToNat k a.1 + ((wiedemannToNat k a.2) <<< (2 ^ k))

def wiedemannOfNat : (k : Nat) → Nat → TowerElem k
  | 0, n => n.testBit 0
  | k + 1, n => (wiedemannOfNat k (n % (2 ^ (2 ^ k))), wiedemannOfNat k (n >>> (2 ^ k)))

def wiedemannPack128 (a : Tower128) : BitVec 128 :=
  BitVec.ofNat 128 (wiedemannToNat 7 a)

def wiedemannUnpack128 (v : BitVec 128) : Tower128 :=
  wiedemannOfNat 7 v.toNat

/-- Fast 3-way Karatsuba evaluator for `TowerElem k`, proved equal to `towerMul k`. -/
def wiedemannKaratsuba : (k : Nat) → TowerElem k → TowerElem k → TowerElem k
  | 0, a, b => a && b
  | k + 1, a, b =>
    let p := wiedemannKaratsuba k a.1 b.1
    let q := wiedemannKaratsuba k a.2 b.2
    let r := wiedemannKaratsuba k (towerAdd k a.1 a.2) (towerAdd k b.1 b.2)
    (towerAdd k p q, towerAdd k (towerAdd k r (towerAdd k p q)) (towerScaleX k q))

theorem wiedemannKaratsuba_eq_towerMul (k : Nat) (a b : TowerElem k) :
    wiedemannKaratsuba k a b = towerMul k a b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [wiedemannKaratsuba, ih, towerMul, towerMul_add_distrib,
      towerAdd_mul_distrib, towerScaleX_eq_mul]
    congr 1
    simp only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm,
      towerAdd_self_zero, towerAdd_zero, towerAdd_cancel]

/-! ### The Rust polynomial basis is a field isomorphic to `Tower128`

Ring laws are proved directly on the shift-and-reduce loop: multiplication by
`b` is the polynomial `b` evaluated at the linear operator `rustGf128MulX`, and
polynomials in one operator commute. The seven Wiedemann generators are then
located inside the Rust basis, which gives a ring homomorphism out of the tower
field; its inverse is Horner evaluation at a root of
`x^128 + x^7 + x^2 + x + 1` in the tower. -/

/-- `Σ_{i<n, f i} X^i · x`: the bits `f` of one multiplicand act on the other. -/
def rustPolyAct : Nat → (Nat → Bool) → RustGf128 → RustGf128
  | 0, _, _ => 0#128
  | n + 1, f, x =>
    (if f 0 then x else 0#128) ^^^ rustPolyAct n (fun i => f (i + 1)) (rustGf128MulX x)

private theorem bxor_left_comm (a b c : RustGf128) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

private theorem bxor_cancel (a b : RustGf128) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem rustGf128MulLoop_eq (n : Nat) : ∀ (x y acc : RustGf128),
    rustGf128MulLoop n x y acc = acc ^^^ rustPolyAct n y.getLsbD x := by
  induction n with
  | zero =>
    intro x y acc
    show acc = acc ^^^ 0#128
    rw [BitVec.xor_zero]
  | succ n ih =>
    intro x y acc
    have hShift : (y >>> 1).getLsbD = fun i => y.getLsbD (i + 1) := by
      funext i
      rw [BitVec.getLsbD_ushiftRight, Nat.add_comm]
    show rustGf128MulLoop n (rustGf128MulX x) (y >>> 1)
        (acc ^^^ (if y.getLsbD 0 then x else 0#128)) =
      acc ^^^ ((if y.getLsbD 0 then x else 0#128) ^^^
        rustPolyAct n (fun i => y.getLsbD (i + 1)) (rustGf128MulX x))
    rw [ih, hShift, BitVec.xor_assoc]

theorem rustGf128Mul_eq_act (a b : RustGf128) :
    rustGf128Mul a b = rustPolyAct 128 b.getLsbD a := by
  unfold rustGf128Mul
  rw [rustGf128MulLoop_eq, BitVec.zero_xor]

private theorem rustGf128MulX_zero : rustGf128MulX 0#128 = 0#128 := by decide

private theorem ite_xor_split (c d : Bool) (k p q : RustGf128) :
    (p ^^^ q) ^^^ (if (c ^^ d) = true then k else 0#128) =
      (p ^^^ (if c = true then k else 0#128)) ^^^ (q ^^^ (if d = true then k else 0#128)) := by
  cases c <;> cases d
  · show (p ^^^ q) ^^^ 0#128 = (p ^^^ 0#128) ^^^ (q ^^^ 0#128)
    simp only [BitVec.xor_zero]
  · show (p ^^^ q) ^^^ k = (p ^^^ 0#128) ^^^ (q ^^^ k)
    simp only [BitVec.xor_zero, BitVec.xor_assoc]
  · show (p ^^^ q) ^^^ k = (p ^^^ k) ^^^ (q ^^^ 0#128)
    simp only [BitVec.xor_zero, BitVec.xor_comm, bxor_left_comm]
  · show (p ^^^ q) ^^^ 0#128 = (p ^^^ k) ^^^ (q ^^^ k)
    simp only [BitVec.xor_zero, BitVec.xor_assoc, BitVec.xor_comm, bxor_left_comm, bxor_cancel]

private theorem rustGf128MulX_xor (a b : RustGf128) :
    rustGf128MulX (a ^^^ b) = rustGf128MulX a ^^^ rustGf128MulX b := by
  unfold rustGf128MulX
  rw [BitVec.shiftLeft_xor_distrib, BitVec.getLsbD_xor]
  exact ite_xor_split _ _ _ _ _

private theorem rustGf128MulX_ite (c : Bool) (x : RustGf128) :
    rustGf128MulX (if c then x else 0#128) = if c then rustGf128MulX x else 0#128 := by
  cases c
  · exact rustGf128MulX_zero
  · rfl

theorem rustPolyAct_zero (n : Nat) : ∀ f, rustPolyAct n f 0#128 = 0#128 := by
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
    intro f
    simp only [rustPolyAct]
    rw [rustGf128MulX_zero, ih]
    cases f 0 <;> decide

theorem rustPolyAct_xor (n : Nat) : ∀ f x y,
    rustPolyAct n f (x ^^^ y) = rustPolyAct n f x ^^^ rustPolyAct n f y := by
  induction n with
  | zero => intro f x y; simp only [rustPolyAct, BitVec.xor_zero]
  | succ n ih =>
    intro f x y
    simp only [rustPolyAct]
    rw [rustGf128MulX_xor, ih]
    generalize rustPolyAct n (fun i => f (i + 1)) (rustGf128MulX x) = P
    generalize rustPolyAct n (fun i => f (i + 1)) (rustGf128MulX y) = Q
    cases f 0
    · show 0#128 ^^^ (P ^^^ Q) = (0#128 ^^^ P) ^^^ (0#128 ^^^ Q)
      simp only [BitVec.zero_xor]
    · show (x ^^^ y) ^^^ (P ^^^ Q) = (x ^^^ P) ^^^ (y ^^^ Q)
      simp only [BitVec.xor_assoc, bxor_left_comm]

private theorem rustPolyAct_ite (n : Nat) (f : Nat → Bool) (c : Bool) (x : RustGf128) :
    rustPolyAct n f (if c then x else 0#128) = if c then rustPolyAct n f x else 0#128 := by
  cases c
  · exact rustPolyAct_zero n f
  · rfl

theorem rustPolyAct_mulX (n : Nat) : ∀ f x,
    rustPolyAct n f (rustGf128MulX x) = rustGf128MulX (rustPolyAct n f x) := by
  induction n with
  | zero => intro f x; exact rustGf128MulX_zero.symm
  | succ n ih =>
    intro f x
    simp only [rustPolyAct]
    rw [rustGf128MulX_xor, rustGf128MulX_ite, ih (fun i => f (i + 1)) (rustGf128MulX x)]

/-- Polynomials in the single operator `rustGf128MulX` commute. -/
theorem rustPolyAct_comm (n m : Nat) (h : Nat → Bool) : ∀ f x,
    rustPolyAct n f (rustPolyAct m h x) = rustPolyAct m h (rustPolyAct n f x) := by
  induction n with
  | zero => intro f x; exact (rustPolyAct_zero m h).symm
  | succ n ih =>
    intro f x
    simp only [rustPolyAct]
    rw [rustPolyAct_xor, rustPolyAct_ite, ← rustPolyAct_mulX m h x,
      ih (fun i => f (i + 1)) (rustGf128MulX x)]

private theorem twoPow_bit (j i : Nat) (hj : j < 128) :
    (BitVec.twoPow 128 j).getLsbD i = decide (j = i) := by
  rw [BitVec.getLsbD_twoPow, decide_eq_true hj]
  rfl

private theorem ite_twoPow_bit (c : Bool) (j i : Nat) (hj : j < 128) :
    (if c then BitVec.twoPow 128 j else 0#128).getLsbD i = (c && decide (j = i)) := by
  cases c
  · exact BitVec.getLsbD_zero
  · exact twoPow_bit j i hj

private theorem rustGf128MulX_twoPow (j : Nat) (hj : j < 127) :
    rustGf128MulX (BitVec.twoPow 128 j) = BitVec.twoPow 128 (j + 1) := by
  unfold rustGf128MulX
  rw [twoPow_bit j 127 (by omega), decide_eq_false (by omega : ¬ j = 127)]
  show (1#128 <<< j) <<< 1 ^^^ 0#128 = 1#128 <<< (j + 1)
  rw [BitVec.xor_zero, BitVec.shiftLeft_add]

/-- No reduction happens below degree 128: the action on `X^j` writes the bits
    of `f` at positions `j, …, j+n-1`. -/
theorem rustPolyAct_twoPow_bit (n : Nat) : ∀ (j : Nat) (f : Nat → Bool), j + n ≤ 128 → ∀ i,
    (rustPolyAct n f (BitVec.twoPow 128 j)).getLsbD i =
      (decide (j ≤ i) && decide (i < j + n) && f (i - j)) := by
  induction n with
  | zero =>
    intro j f _ i
    show (0#128).getLsbD i = _
    rw [BitVec.getLsbD_zero]
    by_cases h : j ≤ i
    · rw [decide_eq_false (by omega : ¬ i < j + 0)]
      simp only [Bool.and_false, Bool.false_and]
    · rw [decide_eq_false h]
      rfl
  | succ n ih =>
    intro j f hjn i
    have hj : j < 128 := by omega
    simp only [rustPolyAct]
    rw [BitVec.getLsbD_xor, ite_twoPow_bit _ j i hj]
    have hRest : (rustPolyAct n (fun i => f (i + 1))
          (rustGf128MulX (BitVec.twoPow 128 j))).getLsbD i =
        (decide (j + 1 ≤ i) && decide (i < j + (n + 1)) && f (i - (j + 1) + 1)) := by
      by_cases hn : n = 0
      · subst hn
        show (0#128).getLsbD i = _
        rw [BitVec.getLsbD_zero]
        by_cases h : j + 1 ≤ i
        · rw [decide_eq_false (by omega : ¬ i < j + (0 + 1))]
          simp only [Bool.and_false, Bool.false_and]
        · rw [decide_eq_false h]
          rfl
      · rw [rustGf128MulX_twoPow j (by omega), ih (j + 1) _ (by omega) i,
          show j + 1 + n = j + (n + 1) from by omega]
    rw [hRest]
    rcases Nat.lt_trichotomy i j with h | h | h
    · rw [decide_eq_false (by omega : ¬ j = i), decide_eq_false (by omega : ¬ j + 1 ≤ i),
        decide_eq_false (by omega : ¬ j ≤ i)]
      cases f 0 <;> rfl
    · subst h
      rw [decide_eq_true (Eq.refl i), decide_eq_false (by omega : ¬ i + 1 ≤ i),
        decide_eq_true (Nat.le_refl i), decide_eq_true (by omega : i < i + (n + 1)),
        Nat.sub_self]
      cases f 0 <;> rfl
    · rw [decide_eq_false (by omega : ¬ j = i), decide_eq_true (by omega : j + 1 ≤ i),
        decide_eq_true (by omega : j ≤ i), show i - (j + 1) + 1 = i - j from by omega]
      cases f 0 <;> cases decide (i < j + (n + 1)) <;> cases f (i - j) <;> rfl

/-- Every element is its own bit polynomial applied to `1`. -/
theorem rustPolyAct_bits_one (a : RustGf128) : rustPolyAct 128 a.getLsbD 1#128 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := rustPolyAct_twoPow_bit 128 0 a.getLsbD (by omega) i
  rw [show BitVec.twoPow 128 0 = 1#128 from by decide] at h
  rw [h, decide_eq_true (Nat.zero_le i), decide_eq_true (by omega : i < 0 + 128), Nat.sub_zero]
  rfl

theorem rustGf128Mul_comm (a b : RustGf128) : rustGf128Mul a b = rustGf128Mul b a := by
  rw [rustGf128Mul_eq_act, rustGf128Mul_eq_act]
  calc rustPolyAct 128 b.getLsbD a
      = rustPolyAct 128 b.getLsbD (rustPolyAct 128 a.getLsbD 1#128) := by
        rw [rustPolyAct_bits_one]
    _ = rustPolyAct 128 a.getLsbD (rustPolyAct 128 b.getLsbD 1#128) :=
        rustPolyAct_comm 128 128 a.getLsbD b.getLsbD 1#128
    _ = rustPolyAct 128 a.getLsbD b := by rw [rustPolyAct_bits_one]

theorem rustGf128Mul_xor_left (a b c : RustGf128) :
    rustGf128Mul (a ^^^ b) c = rustGf128Mul a c ^^^ rustGf128Mul b c := by
  simp only [rustGf128Mul_eq_act, rustPolyAct_xor]

theorem rustGf128Mul_xor_right (a b c : RustGf128) :
    rustGf128Mul a (b ^^^ c) = rustGf128Mul a b ^^^ rustGf128Mul a c := by
  rw [rustGf128Mul_comm a, rustGf128Mul_xor_left, rustGf128Mul_comm b a, rustGf128Mul_comm c a]

theorem rustGf128Mul_assoc (a b c : RustGf128) :
    rustGf128Mul (rustGf128Mul a b) c = rustGf128Mul a (rustGf128Mul b c) := by
  rw [rustGf128Mul_comm a (rustGf128Mul b c), rustGf128Mul_comm a b]
  simp only [rustGf128Mul_eq_act]
  exact rustPolyAct_comm 128 128 a.getLsbD c.getLsbD b

theorem rustGf128Mul_left_comm (a b c : RustGf128) :
    rustGf128Mul a (rustGf128Mul b c) = rustGf128Mul b (rustGf128Mul a c) := by
  rw [← rustGf128Mul_assoc, rustGf128Mul_comm a b, rustGf128Mul_assoc]

theorem rustGf128Mul_one_left (a : RustGf128) : rustGf128Mul 1#128 a = a := by
  rw [rustGf128Mul_eq_act, rustPolyAct_bits_one]

theorem rustGf128Mul_one_right (a : RustGf128) : rustGf128Mul a 1#128 = a := by
  rw [rustGf128Mul_comm, rustGf128Mul_one_left]

theorem rustGf128Mul_zero_left (a : RustGf128) : rustGf128Mul 0#128 a = 0#128 := by
  rw [rustGf128Mul_eq_act, rustPolyAct_zero]

theorem rustGf128Mul_zero_right (a : RustGf128) : rustGf128Mul a 0#128 = 0#128 := by
  rw [rustGf128Mul_comm, rustGf128Mul_zero_left]

theorem rustGf128MulX_eq_mul (a : RustGf128) : rustGf128MulX a = rustGf128Mul 2#128 a := by
  rw [rustGf128Mul_eq_act, show (2#128 : RustGf128) = rustGf128MulX 1#128 from by decide,
    rustPolyAct_mulX, rustPolyAct_bits_one]

/-- The Rust polynomial basis as a commutative ring: addition is XOR and
    multiplication is the shift-and-reduce loop. Scoped so that no other
    `BitVec 128` carrier silently inherits this multiplication. -/
scoped instance rustGf128Ring : LawfulCommRing RustGf128 where
  zero := 0#128
  one := 1#128
  add a b := a ^^^ b
  mul := rustGf128Mul
  neg a := a
  sub a b := a ^^^ b
  add_assoc := BitVec.xor_assoc
  add_comm := BitVec.xor_comm
  zero_add _ := BitVec.zero_xor
  add_zero _ := BitVec.xor_zero
  add_left_neg _ := BitVec.xor_self
  sub_eq_add_neg _ _ := rfl
  mul_assoc := rustGf128Mul_assoc
  mul_comm := rustGf128Mul_comm
  one_mul := rustGf128Mul_one_left
  mul_one := rustGf128Mul_one_right
  left_distrib := rustGf128Mul_xor_right
  right_distrib := rustGf128Mul_xor_left

/-- Images of the Wiedemann generators `t_k` (`t_0 = 1`,
    `t_{k+1}^2 = t_{k+1} t_k + 1`) in the Rust basis. -/
def towerGenRust : Nat → RustGf128
  | 0 => 1#128
  | 1 => 0x295ac0b1f4731af9676aac9fa4b20b08#128
  | 2 => 0x500317bd159d73bb34d2f7fba603e341#128
  | 3 => 0xd7272761ca8e287777eda49fad5950db#128
  | 4 => 0xf7ee5366ad8dcdf077be5724c64eb1d2#128
  | 5 => 0x218cc1384d3fe56b1428b68814f535be#128
  | 6 => 0x2c2fcdaa2679817f994e36d0d1df3b3d#128
  | 7 => 0xe4f21e8c8ec8031cb7b73094152f7631#128
  | _ => 0#128

theorem towerGenRust_sq (k : Nat) (hk : k < 7) :
    rustGf128Mul (towerGenRust (k + 1)) (towerGenRust (k + 1)) =
      rustGf128Mul (towerGenRust (k + 1)) (towerGenRust k) ^^^ 1#128 := by
  have h : ∀ k : Fin 7,
      rustGf128Mul (towerGenRust (k.val + 1)) (towerGenRust (k.val + 1)) =
        rustGf128Mul (towerGenRust (k.val + 1)) (towerGenRust k.val) ^^^ 1#128 := by
    decide +kernel
  exact h ⟨k, hk⟩

/-- The tower embedded in the Rust basis, one quadratic extension at a time. -/
def towerToRust : (k : Nat) → TowerElem k → RustGf128
  | 0, a => match a with | true => 1#128 | false => 0#128
  | k + 1, a =>
    towerToRust k a.1 ^^^ rustGf128Mul (towerToRust k a.2) (towerGenRust (k + 1))

theorem towerToRust_zero (k : Nat) : towerToRust k (towerZero k) = 0#128 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show towerToRust k (towerZero k) ^^^
      rustGf128Mul (towerToRust k (towerZero k)) (towerGenRust (k + 1)) = 0#128
    rw [ih, rustGf128Mul_zero_left, BitVec.xor_zero]

theorem towerToRust_one (k : Nat) : towerToRust k (towerOne k) = 1#128 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show towerToRust k (towerOne k) ^^^
      rustGf128Mul (towerToRust k (towerZero k)) (towerGenRust (k + 1)) = 1#128
    rw [ih, towerToRust_zero, rustGf128Mul_zero_left, BitVec.xor_zero]

theorem towerToRust_add (k : Nat) (a b : TowerElem k) :
    towerToRust k (towerAdd k a b) = towerToRust k a ^^^ towerToRust k b := by
  induction k with
  | zero => cases a <;> cases b <;> decide
  | succ k ih =>
    show towerToRust k (towerAdd k a.1 b.1) ^^^
        rustGf128Mul (towerToRust k (towerAdd k a.2 b.2)) (towerGenRust (k + 1)) =
      (towerToRust k a.1 ^^^ rustGf128Mul (towerToRust k a.2) (towerGenRust (k + 1))) ^^^
      (towerToRust k b.1 ^^^ rustGf128Mul (towerToRust k b.2) (towerGenRust (k + 1)))
    rw [ih, ih, rustGf128Mul_xor_left]
    simp only [BitVec.xor_assoc, bxor_left_comm]

theorem towerToRust_X (k : Nat) : towerToRust k (towerX k) = towerGenRust k := by
  cases k with
  | zero => rfl
  | succ k =>
    show towerToRust k (towerZero k) ^^^
      rustGf128Mul (towerToRust k (towerOne k)) (towerGenRust (k + 1)) = towerGenRust (k + 1)
    rw [towerToRust_zero, towerToRust_one, rustGf128Mul_one_left, BitVec.zero_xor]

set_option linter.unusedSimpArgs false in
private theorem rust_tower_step (A1 A2 B1 B2 T U : RustGf128)
    (hT : rustGf128Mul T T = rustGf128Mul T U ^^^ 1#128) :
    (rustGf128Mul A1 B1 ^^^ rustGf128Mul A2 B2) ^^^
      rustGf128Mul ((rustGf128Mul A1 B2 ^^^ rustGf128Mul A2 B1) ^^^
        rustGf128Mul U (rustGf128Mul A2 B2)) T =
    rustGf128Mul (A1 ^^^ rustGf128Mul A2 T) (B1 ^^^ rustGf128Mul B2 T) := by
  have hs : rustGf128Mul (rustGf128Mul A2 T) (rustGf128Mul B2 T) =
      rustGf128Mul (rustGf128Mul A2 B2) (rustGf128Mul T T) := by
    simp only [rustGf128Mul_comm, rustGf128Mul_left_comm]
  have h4 : rustGf128Mul (rustGf128Mul A2 T) (rustGf128Mul B2 T) =
      rustGf128Mul (rustGf128Mul A2 B2) (rustGf128Mul T U) ^^^ rustGf128Mul A2 B2 := by
    rw [hs, hT, rustGf128Mul_xor_right, rustGf128Mul_one_right]
  rw [rustGf128Mul_xor_left A1 (rustGf128Mul A2 T), rustGf128Mul_xor_right A1,
    rustGf128Mul_xor_right (rustGf128Mul A2 T), h4]
  simp only [rustGf128Mul_xor_right, rustGf128Mul_comm,
    rustGf128Mul_left_comm, BitVec.xor_assoc, BitVec.xor_comm, bxor_left_comm]

theorem towerToRust_mul : ∀ (k : Nat), k ≤ 7 → ∀ a b : TowerElem k,
    towerToRust k (towerMul k a b) =
      rustGf128Mul (towerToRust k a) (towerToRust k b) := by
  intro k
  induction k with
  | zero => intro _ a b; cases a <;> cases b <;> decide +kernel
  | succ k ih =>
    intro hk a b
    have ih' := ih (by omega)
    show towerToRust k (towerAdd k (towerMul k a.1 b.1) (towerMul k a.2 b.2)) ^^^
        rustGf128Mul (towerToRust k (towerAdd k
          (towerAdd k (towerMul k a.1 b.2) (towerMul k a.2 b.1))
          (towerMul k (towerX k) (towerMul k a.2 b.2)))) (towerGenRust (k + 1)) =
      rustGf128Mul (towerToRust k a.1 ^^^ rustGf128Mul (towerToRust k a.2) (towerGenRust (k + 1)))
        (towerToRust k b.1 ^^^ rustGf128Mul (towerToRust k b.2) (towerGenRust (k + 1)))
    simp only [towerToRust_add, ih', towerToRust_X]
    exact rust_tower_step _ _ _ _ _ _ (towerGenRust_sq k (by omega))

/-- A ring homomorphism out of a field is injective. -/
theorem towerToRust_injective (a b : Tower128)
    (h : towerToRust 7 a = towerToRust 7 b) : a = b := by
  have hsum : towerToRust 7 (towerAdd 7 a b) = 0#128 := by
    rw [towerToRust_add, h, BitVec.xor_self]
  by_cases hz : towerAdd 7 a b = towerZero 7
  · have hc := towerAdd_cancel 7 a b
    rw [hz, towerAdd_zero] at hc
    exact hc
  · exfalso
    have h1 := congrArg (towerToRust 7) (towerMul_inv 7 _ hz)
    rw [towerToRust_mul 7 (Nat.le_refl 7), hsum, rustGf128Mul_zero_left, towerToRust_one] at h1
    exact absurd h1 (by decide)

/-- A root of `x^128 + x^7 + x^2 + x + 1` in the Wiedemann tower: the image of
    Rust's `x` (`2#128`). -/
def rustGenTower : Tower128 :=
  wiedemannOfNat 7 0xbfe0a17ee2b77754526b13e1fedaef3d

theorem towerToRust_rustGenTower : towerToRust 7 rustGenTower = 2#128 := by
  decide +kernel

def rustToTowerAux : Nat → (Nat → Bool) → Tower128
  | 0, _ => towerZero 7
  | n + 1, f =>
    towerAdd 7 (if f 0 then towerOne 7 else towerZero 7)
      (towerMul 7 rustGenTower (rustToTowerAux n (fun i => f (i + 1))))

/-- The basis conversion: Horner evaluation of the Rust coefficient bits at
    `rustGenTower`. This, not coordinate repacking, relates the two carriers. -/
def rustToTower (a : RustGf128) : Tower128 := rustToTowerAux 128 a.getLsbD

private theorem towerToRust_bit (c : Bool) :
    towerToRust 7 (if c then towerOne 7 else towerZero 7) = if c then 1#128 else 0#128 := by
  cases c
  · exact towerToRust_zero 7
  · exact towerToRust_one 7

theorem towerToRust_rustToTowerAux (n : Nat) : ∀ f,
    towerToRust 7 (rustToTowerAux n f) = rustPolyAct n f 1#128 := by
  induction n with
  | zero => intro f; exact towerToRust_zero 7
  | succ n ih =>
    intro f
    simp only [rustToTowerAux, rustPolyAct]
    rw [towerToRust_add, towerToRust_mul 7 (Nat.le_refl 7), towerToRust_rustGenTower, ih,
      towerToRust_bit, rustPolyAct_mulX, rustGf128MulX_eq_mul]

theorem towerToRust_rustToTower (a : RustGf128) : towerToRust 7 (rustToTower a) = a := by
  unfold rustToTower
  rw [towerToRust_rustToTowerAux, rustPolyAct_bits_one]

theorem rustToTower_towerToRust (t : Tower128) : rustToTower (towerToRust 7 t) = t :=
  towerToRust_injective _ _ (towerToRust_rustToTower _)

theorem rustToTower_injective (a b : RustGf128) (h : rustToTower a = rustToTower b) : a = b := by
  have hc := congrArg (towerToRust 7) h
  rw [towerToRust_rustToTower, towerToRust_rustToTower] at hc
  exact hc

theorem rustToTower_xor (a b : RustGf128) :
    rustToTower (a ^^^ b) = towerAdd 7 (rustToTower a) (rustToTower b) := by
  apply towerToRust_injective
  rw [towerToRust_rustToTower, towerToRust_add, towerToRust_rustToTower, towerToRust_rustToTower]

/-- The conversion carries Rust's multiplication to tower multiplication for
    every pair of field elements. -/
theorem rustToTower_mul (a b : RustGf128) :
    rustToTower (rustGf128Mul a b) = towerMul 7 (rustToTower a) (rustToTower b) := by
  apply towerToRust_injective
  rw [towerToRust_rustToTower, towerToRust_mul 7 (Nat.le_refl 7), towerToRust_rustToTower,
    towerToRust_rustToTower]

theorem rustToTower_zero : rustToTower 0#128 = towerZero 7 := by
  apply towerToRust_injective
  rw [towerToRust_rustToTower, towerToRust_zero]

theorem rustToTower_two : rustToTower 2#128 = rustGenTower := by
  apply towerToRust_injective
  rw [towerToRust_rustToTower, towerToRust_rustGenTower]

/-- `x^128 + x^7 + x^2 + x + 1` has no proper factorisation: the quotient ring
    Rust computes in has no zero divisors. -/
theorem rustGf128Mul_eq_zero (a b : RustGf128) (h : rustGf128Mul a b = 0#128) :
    a = 0#128 ∨ b = 0#128 := by
  have ht : towerMul 7 (rustToTower a) (rustToTower b) = towerZero 7 := by
    rw [← rustToTower_mul, h, rustToTower_zero]
  rcases (towerMul_eq_zero_iff 7 _ _).mp ht with h1 | h1
  · exact Or.inl (rustToTower_injective _ _ (h1.trans rustToTower_zero.symm))
  · exact Or.inr (rustToTower_injective _ _ (h1.trans rustToTower_zero.symm))

scoped instance rustGf128NoZeroDivisors : NoZeroDivisors RustGf128 where
  eq_zero_or_eq_zero_of_mul_eq_zero h := rustGf128Mul_eq_zero _ _ h


end MigrationExecution
/-- Constructive bijectivity predicate (`injective ∧ surjective`). -/
@[expose] def IsBijective {α β : Type} (f : α → β) : Prop :=
  (∀ a b : α, f a = f b → a = b) ∧ (∀ b : β, ∃ a : α, f a = b)

private def poly128Xtimes (a : BitVec 128) : BitVec 128 :=
  if a.getLsbD 127 then (a <<< 1) ^^^ 0x87#128 else a <<< 1

private def poly128ShiftPow : Nat → BitVec 128 → BitVec 128
  | 0, a => poly128Xtimes a
  | k + 1, a => poly128ShiftPow k (poly128ShiftPow k a)

private def poly128MulRange : Nat → BitVec 128 → BitVec 128 → BitVec 128
  | 0, a, b => if b.getLsbD 0 then a else 0#128
  | k + 1, a, b =>
    poly128MulRange k a b ^^^ poly128MulRange k (poly128ShiftPow k a) (b >>> (2 ^ k))

/-- Equal to the Rust `gf2_128_mul` loop model: `gf2_128_mul_bv_eq_rustGf128Mul`. -/
def gf2_128_mul_bv (a b : BitVec 128) : BitVec 128 := poly128MulRange 7 a b

private def tower128PolyGen : Fin 7 → BitVec 128
  | ⟨0, _⟩ => 0x295ac0b1f4731af9676aac9fa4b20b08#128
  | ⟨1, _⟩ => 0x500317bd159d73bb34d2f7fba603e341#128
  | ⟨2, _⟩ => 0x872430dcdf135bcc433f53640b5ab39a#128
  | ⟨3, _⟩ => 0x08ee6d05a2afa6e5f848729a9637483a#128
  | ⟨4, _⟩ => 0x6167c15ae3f2515951c65cfffdd09b94#128
  | ⟨5, _⟩ => 0x11bf2ae00eefb7458f1990f8ffd4b9bc#128
  | ⟨6, _⟩ => 0x8845a6b78c9fffc36a2a74600cfa98de#128

set_option maxRecDepth 4096

private def psiRec : (k : Nat) → (hk : k ≤ 7) → TowerElem k → BitVec 128
  | 0, _, a => match (a : Bool) with | true => 1#128 | false => 0#128
  | k + 1, hk, (a0, a1) =>
    psiRec k (Nat.le_of_succ_le hk) a0 ^^^
      gf2_128_mul_bv (tower128PolyGen ⟨k, hk⟩) (psiRec k (Nat.le_of_succ_le hk) a1)

/-- A field isomorphism: `Tower128PolyBasisIso.psiTower128ToPoly_field_isomorphism`. -/
def psiTower128ToPoly (x : Tower128) : BitVec 128 := psiRec 7 (Nat.le_refl 7) x

end Qsag
namespace Qsag
open MigrationExecution

set_option autoImplicit false

/-! ## 1. `gf2_128_mul_bv` is the Rust shift-and-reduce loop -/

private theorem gf128_xor_left_comm (a b c : BitVec 128) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

private theorem poly128Xtimes_eq_rustMulX (a : BitVec 128) :
    poly128Xtimes a = rustGf128MulX a := by
  unfold poly128Xtimes rustGf128MulX
  cases a.getLsbD 127
  · exact BitVec.xor_zero.symm
  · rfl

/-- `n` applications of multiplication by `x`. -/
def rustGf128MulXIter : Nat → BitVec 128 → BitVec 128
  | 0, a => a
  | n + 1, a => rustGf128MulXIter n (rustGf128MulX a)

theorem rustGf128MulXIter_add : ∀ (m n : Nat) (a : BitVec 128),
    rustGf128MulXIter (m + n) a = rustGf128MulXIter n (rustGf128MulXIter m a)
  | 0, n, a => by rw [Nat.zero_add]; rfl
  | m + 1, n, a => by
    rw [Nat.succ_add]
    exact rustGf128MulXIter_add m n (rustGf128MulX a)

private theorem poly128ShiftPow_eq_iter : ∀ (k : Nat) (a : BitVec 128),
    poly128ShiftPow k a = rustGf128MulXIter (2 ^ k) a
  | 0, a => poly128Xtimes_eq_rustMulX a
  | k + 1, a => by
    show poly128ShiftPow k (poly128ShiftPow k a) = _
    rw [poly128ShiftPow_eq_iter k, poly128ShiftPow_eq_iter k, Nat.pow_succ, Nat.mul_two,
      rustGf128MulXIter_add]

/-- The bit polynomial of a multiplicand splits at any degree. -/
theorem rustPolyAct_split : ∀ (m n : Nat) (f : Nat → Bool) (x : BitVec 128),
    rustPolyAct (m + n) f x =
      rustPolyAct m f x ^^^ rustPolyAct n (fun i => f (i + m)) (rustGf128MulXIter m x)
  | 0, n, f, x => by
    rw [Nat.zero_add]
    exact (BitVec.zero_xor).symm
  | m + 1, n, f, x => by
    rw [Nat.succ_add]
    show (if f 0 then x else 0#128) ^^^
        rustPolyAct (m + n) (fun i => f (i + 1)) (rustGf128MulX x) =
      ((if f 0 then x else 0#128) ^^^ rustPolyAct m (fun i => f (i + 1)) (rustGf128MulX x)) ^^^
        rustPolyAct n (fun i => f (i + (m + 1))) (rustGf128MulXIter m (rustGf128MulX x))
    rw [rustPolyAct_split m n, BitVec.xor_assoc]
    rfl

private theorem poly128MulRange_eq_act : ∀ (k : Nat) (a b : BitVec 128),
    poly128MulRange k a b = rustPolyAct (2 ^ k) b.getLsbD a
  | 0, a, b => by
    show (if b.getLsbD 0 then a else 0#128) = (if b.getLsbD 0 then a else 0#128) ^^^ 0#128
    rw [BitVec.xor_zero]
  | k + 1, a, b => by
    have hShift : (b >>> (2 ^ k)).getLsbD = fun i => b.getLsbD (i + 2 ^ k) := by
      funext i
      rw [BitVec.getLsbD_ushiftRight, Nat.add_comm]
    show poly128MulRange k a b ^^^ poly128MulRange k (poly128ShiftPow k a) (b >>> (2 ^ k)) = _
    rw [poly128MulRange_eq_act k, poly128MulRange_eq_act k, poly128ShiftPow_eq_iter, hShift,
      Nat.pow_succ, Nat.mul_two, rustPolyAct_split]

/-- **The definition used by `psiTower128ToPoly` is the Rust loop**, for all inputs. -/
theorem gf2_128_mul_bv_eq_rustGf128Mul (a b : BitVec 128) :
    gf2_128_mul_bv a b = rustGf128Mul a b := by
  unfold gf2_128_mul_bv
  rw [poly128MulRange_eq_act, rustGf128Mul_eq_act]

theorem gf2_128_mul_bv_comm (a b : BitVec 128) : gf2_128_mul_bv a b = gf2_128_mul_bv b a := by
  simp only [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_comm a b]

theorem gf2_128_mul_bv_assoc (a b c : BitVec 128) :
    gf2_128_mul_bv (gf2_128_mul_bv a b) c = gf2_128_mul_bv a (gf2_128_mul_bv b c) := by
  simp only [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_assoc]

theorem gf2_128_mul_bv_xor_right (a b c : BitVec 128) :
    gf2_128_mul_bv a (b ^^^ c) = gf2_128_mul_bv a b ^^^ gf2_128_mul_bv a c := by
  simp only [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_xor_right]

theorem gf2_128_mul_bv_xor_left (a b c : BitVec 128) :
    gf2_128_mul_bv (a ^^^ b) c = gf2_128_mul_bv a c ^^^ gf2_128_mul_bv b c := by
  simp only [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_xor_left]

theorem gf2_128_mul_bv_one_left (a : BitVec 128) : gf2_128_mul_bv 1#128 a = a := by
  rw [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_one_left]

theorem gf2_128_mul_bv_one_right (a : BitVec 128) : gf2_128_mul_bv a 1#128 = a := by
  rw [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_one_right]

/-! ## 2. The generator recursion as a level-indexed map -/

/-- Image of the level-`k` Wiedemann generator `towerX k`: `1` at level `0`, then
    `TOWER128_POLY_GENERATORS[k - 1]`. -/
def tower128PolyGenLevel : Nat → BitVec 128
  | 0 => 1#128
  | k + 1 => if h : k < 7 then tower128PolyGen ⟨k, h⟩ else 0#128

/-- `psiTower128ToPoly` at every tower level, with multiplication written as the Rust loop. -/
def towerToPolyBasis : (k : Nat) → TowerElem k → BitVec 128
  | 0, a => match (a : Bool) with | true => 1#128 | false => 0#128
  | k + 1, a =>
    towerToPolyBasis k a.1 ^^^
      rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k a.2)

private theorem psiRec_eq_towerToPolyBasis : ∀ (k : Nat) (hk : k ≤ 7) (a : TowerElem k),
    psiRec k hk a = towerToPolyBasis k a
  | 0, _, _ => rfl
  | k + 1, hk, a => by
    rcases a with ⟨a0, a1⟩
    have hGen : tower128PolyGenLevel (k + 1) = tower128PolyGen ⟨k, hk⟩ := by
      have hk' : k < 7 := hk
      simp only [tower128PolyGenLevel, hk', ↓reduceDIte]
    show psiRec k (Nat.le_of_succ_le hk) a0 ^^^
        gf2_128_mul_bv (tower128PolyGen ⟨k, hk⟩) (psiRec k (Nat.le_of_succ_le hk) a1) =
      towerToPolyBasis k a0 ^^^
        rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k a1)
    rw [psiRec_eq_towerToPolyBasis k _ a0, psiRec_eq_towerToPolyBasis k _ a1,
      gf2_128_mul_bv_eq_rustGf128Mul, hGen]

theorem psiTower128ToPoly_eq_towerToPolyBasis (x : Tower128) :
    psiTower128ToPoly x = towerToPolyBasis 7 x :=
  psiRec_eq_towerToPolyBasis 7 (Nat.le_refl 7) x

theorem towerToPolyBasis_zero : ∀ k : Nat, towerToPolyBasis k (towerZero k) = 0#128
  | 0 => rfl
  | k + 1 => by
    show towerToPolyBasis k (towerZero k) ^^^
      rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k (towerZero k)) = 0#128
    rw [towerToPolyBasis_zero k, rustGf128Mul_zero_right, BitVec.xor_zero]

theorem towerToPolyBasis_one : ∀ k : Nat, towerToPolyBasis k (towerOne k) = 1#128
  | 0 => rfl
  | k + 1 => by
    show towerToPolyBasis k (towerOne k) ^^^
      rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k (towerZero k)) = 1#128
    rw [towerToPolyBasis_one k, towerToPolyBasis_zero, rustGf128Mul_zero_right, BitVec.xor_zero]

theorem towerToPolyBasis_add : ∀ (k : Nat) (a b : TowerElem k),
    towerToPolyBasis k (towerAdd k a b) = towerToPolyBasis k a ^^^ towerToPolyBasis k b
  | 0, a, b => by cases a <;> cases b <;> decide
  | k + 1, a, b => by
    show towerToPolyBasis k (towerAdd k a.1 b.1) ^^^
        rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k (towerAdd k a.2 b.2)) =
      (towerToPolyBasis k a.1 ^^^
        rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k a.2)) ^^^
      (towerToPolyBasis k b.1 ^^^
        rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k b.2))
    rw [towerToPolyBasis_add k, towerToPolyBasis_add k, rustGf128Mul_xor_right]
    simp only [BitVec.xor_assoc, gf128_xor_left_comm]

theorem towerToPolyBasis_X : ∀ k : Nat, towerToPolyBasis k (towerX k) = tower128PolyGenLevel k
  | 0 => rfl
  | k + 1 => by
    show towerToPolyBasis k (towerZero k) ^^^
      rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k (towerOne k)) =
        tower128PolyGenLevel (k + 1)
    rw [towerToPolyBasis_zero, towerToPolyBasis_one, rustGf128Mul_one_right, BitVec.zero_xor]

/-- The seven Artin–Schreier relations `g_k^2 = g_k · g_{k-1} + 1` (`g_{-1} = 1`) hold for the
    Rust generators under the Rust multiplication. Kernel-evaluated. -/
theorem tower128PolyGenLevel_sq (k : Nat) (hk : k < 7) :
    rustGf128Mul (tower128PolyGenLevel (k + 1)) (tower128PolyGenLevel (k + 1)) =
      rustGf128Mul (tower128PolyGenLevel (k + 1)) (tower128PolyGenLevel k) ^^^ 1#128 := by
  have h : ∀ k : Fin 7,
      rustGf128Mul (tower128PolyGenLevel (k.val + 1)) (tower128PolyGenLevel (k.val + 1)) =
        rustGf128Mul (tower128PolyGenLevel (k.val + 1)) (tower128PolyGenLevel k.val) ^^^
          1#128 := by
    decide +kernel
  exact h ⟨k, hk⟩

set_option linter.unusedSimpArgs false in
private theorem gf128_tower_step (A1 A2 B1 B2 T U : BitVec 128)
    (hT : rustGf128Mul T T = rustGf128Mul T U ^^^ 1#128) :
    (rustGf128Mul A1 B1 ^^^ rustGf128Mul A2 B2) ^^^
      rustGf128Mul T ((rustGf128Mul A1 B2 ^^^ rustGf128Mul A2 B1) ^^^
        rustGf128Mul U (rustGf128Mul A2 B2)) =
    rustGf128Mul (A1 ^^^ rustGf128Mul T A2) (B1 ^^^ rustGf128Mul T B2) := by
  have hs : rustGf128Mul (rustGf128Mul T A2) (rustGf128Mul T B2) =
      rustGf128Mul (rustGf128Mul A2 B2) (rustGf128Mul T T) := by
    simp only [rustGf128Mul_comm, rustGf128Mul_left_comm]
  have h4 : rustGf128Mul (rustGf128Mul T A2) (rustGf128Mul T B2) =
      rustGf128Mul (rustGf128Mul A2 B2) (rustGf128Mul T U) ^^^ rustGf128Mul A2 B2 := by
    rw [hs, hT, rustGf128Mul_xor_right, rustGf128Mul_one_right]
  rw [rustGf128Mul_xor_left A1 (rustGf128Mul T A2), rustGf128Mul_xor_right A1,
    rustGf128Mul_xor_right (rustGf128Mul T A2), h4]
  simp only [rustGf128Mul_xor_right, rustGf128Mul_comm,
    rustGf128Mul_left_comm, BitVec.xor_assoc, BitVec.xor_comm, gf128_xor_left_comm]

theorem towerToPolyBasis_mul : ∀ (k : Nat), k ≤ 7 → ∀ a b : TowerElem k,
    towerToPolyBasis k (towerMul k a b) =
      rustGf128Mul (towerToPolyBasis k a) (towerToPolyBasis k b)
  | 0, _, a, b => by cases a <;> cases b <;> decide +kernel
  | k + 1, hk, a, b => by
    have ih := towerToPolyBasis_mul k (Nat.le_of_succ_le hk)
    show towerToPolyBasis k (towerAdd k (towerMul k a.1 b.1) (towerMul k a.2 b.2)) ^^^
        rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k (towerAdd k
          (towerAdd k (towerMul k a.1 b.2) (towerMul k a.2 b.1))
          (towerMul k (towerX k) (towerMul k a.2 b.2)))) =
      rustGf128Mul
        (towerToPolyBasis k a.1 ^^^
          rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k a.2))
        (towerToPolyBasis k b.1 ^^^
          rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k b.2))
    simp only [towerToPolyBasis_add, ih, towerToPolyBasis_X]
    exact gf128_tower_step _ _ _ _ _ _ (tower128PolyGenLevel_sq k hk)

/-! ## 3. `psiTower128ToPoly` is a ring homomorphism for every pair of inputs -/

theorem psiTower128ToPoly_zero : psiTower128ToPoly (towerZero 7) = 0#128 := by
  rw [psiTower128ToPoly_eq_towerToPolyBasis, towerToPolyBasis_zero]

theorem psiTower128ToPoly_one : psiTower128ToPoly (towerOne 7) = 1#128 := by
  rw [psiTower128ToPoly_eq_towerToPolyBasis, towerToPolyBasis_one]

theorem psiTower128ToPoly_add (a b : Tower128) :
    psiTower128ToPoly (towerAdd 7 a b) = psiTower128ToPoly a ^^^ psiTower128ToPoly b := by
  simp only [psiTower128ToPoly_eq_towerToPolyBasis, towerToPolyBasis_add]

/-- Multiplicativity against the literal Rust loop model. -/
theorem psiTower128ToPoly_mul_rust (a b : Tower128) :
    psiTower128ToPoly (towerMul 7 a b) =
      rustGf128Mul (psiTower128ToPoly a) (psiTower128ToPoly b) := by
  simp only [psiTower128ToPoly_eq_towerToPolyBasis, towerToPolyBasis_mul 7 (Nat.le_refl 7)]

theorem psiTower128ToPoly_mul (a b : Tower128) :
    psiTower128ToPoly (towerMul 7 a b) =
      gf2_128_mul_bv (psiTower128ToPoly a) (psiTower128ToPoly b) := by
  rw [gf2_128_mul_bv_eq_rustGf128Mul, psiTower128ToPoly_mul_rust]

/-- A ring homomorphism out of a field is injective. -/
theorem psiTower128ToPoly_injective (a b : Tower128)
    (h : psiTower128ToPoly a = psiTower128ToPoly b) : a = b := by
  have hsum : psiTower128ToPoly (towerAdd 7 a b) = 0#128 := by
    rw [psiTower128ToPoly_add, h, BitVec.xor_self]
  by_cases hz : towerAdd 7 a b = towerZero 7
  · have hc := towerAdd_cancel 7 a b
    rw [hz, towerAdd_zero] at hc
    exact hc
  · exfalso
    have h1 := congrArg psiTower128ToPoly (towerMul_inv 7 _ hz)
    rw [psiTower128ToPoly_mul_rust, hsum, rustGf128Mul_zero_left, psiTower128ToPoly_one] at h1
    exact absurd h1 (by decide)

theorem psiTower128ToPoly_eq_zero_iff (a : Tower128) :
    psiTower128ToPoly a = 0#128 ↔ a = towerZero 7 :=
  ⟨fun h => psiTower128ToPoly_injective a _ (h.trans psiTower128ToPoly_zero.symm),
   fun h => by rw [h, psiTower128ToPoly_zero]⟩

/-! ## 4. Explicit inverse: Horner evaluation at the tower preimage of `x` -/

def polyGenTower128Bits : BitVec 128 := 0xbf72eab170e2403236a22fb2474b2624#128

/-- The tower element whose image is Rust's `x` (`2#128`): a root of
    `x^128 + x^7 + x^2 + x + 1` in `Tower128`, in `packTower` coordinates. -/
def polyGenTower128 : Tower128 := unpackTower 7 polyGenTower128Bits

set_option maxRecDepth 4096 in
theorem psiTower128ToPoly_polyGenTower128 : psiTower128ToPoly polyGenTower128 = 2#128 := by
  decide +kernel

def polyToTower128Aux : Nat → (Nat → Bool) → Tower128
  | 0, _ => towerZero 7
  | n + 1, f =>
    towerAdd 7 (if f 0 then towerOne 7 else towerZero 7)
      (towerMul 7 polyGenTower128 (polyToTower128Aux n (fun i => f (i + 1))))

/-- Inverse basis change: the Rust coefficient word evaluated at `polyGenTower128`. -/
def polyToTower128 (a : BitVec 128) : Tower128 := polyToTower128Aux 128 a.getLsbD

private theorem psiTower128ToPoly_bit (c : Bool) :
    psiTower128ToPoly (if c then towerOne 7 else towerZero 7) = if c then 1#128 else 0#128 := by
  cases c
  · exact psiTower128ToPoly_zero
  · exact psiTower128ToPoly_one

private theorem psiTower128ToPoly_polyToTower128Aux : ∀ (n : Nat) (f : Nat → Bool),
    psiTower128ToPoly (polyToTower128Aux n f) = rustPolyAct n f 1#128
  | 0, _ => psiTower128ToPoly_zero
  | n + 1, f => by
    show psiTower128ToPoly (towerAdd 7 (if f 0 then towerOne 7 else towerZero 7)
        (towerMul 7 polyGenTower128 (polyToTower128Aux n (fun i => f (i + 1))))) =
      (if f 0 then 1#128 else 0#128) ^^^
        rustPolyAct n (fun i => f (i + 1)) (rustGf128MulX 1#128)
    rw [psiTower128ToPoly_add, psiTower128ToPoly_mul_rust, psiTower128ToPoly_polyGenTower128,
      psiTower128ToPoly_polyToTower128Aux n, psiTower128ToPoly_bit, rustPolyAct_mulX,
      rustGf128MulX_eq_mul]

theorem psiTower128ToPoly_polyToTower128 (a : BitVec 128) :
    psiTower128ToPoly (polyToTower128 a) = a := by
  unfold polyToTower128
  rw [psiTower128ToPoly_polyToTower128Aux, rustPolyAct_bits_one]

theorem polyToTower128_psiTower128ToPoly (t : Tower128) :
    polyToTower128 (psiTower128ToPoly t) = t :=
  psiTower128ToPoly_injective _ _ (psiTower128ToPoly_polyToTower128 _)

theorem polyToTower128_injective (a b : BitVec 128)
    (h : polyToTower128 a = polyToTower128 b) : a = b := by
  have hc := congrArg psiTower128ToPoly h
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_polyToTower128] at hc
  exact hc

theorem polyToTower128_zero : polyToTower128 0#128 = towerZero 7 := by
  apply psiTower128ToPoly_injective
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_zero]

theorem polyToTower128_one : polyToTower128 1#128 = towerOne 7 := by
  apply psiTower128ToPoly_injective
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_one]

theorem polyToTower128_xor (a b : BitVec 128) :
    polyToTower128 (a ^^^ b) = towerAdd 7 (polyToTower128 a) (polyToTower128 b) := by
  apply psiTower128ToPoly_injective
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_add,
    psiTower128ToPoly_polyToTower128, psiTower128ToPoly_polyToTower128]

/-- Rust's multiplication is tower multiplication under the inverse basis change. -/
theorem polyToTower128_mul_rust (a b : BitVec 128) :
    polyToTower128 (rustGf128Mul a b) = towerMul 7 (polyToTower128 a) (polyToTower128 b) := by
  apply psiTower128ToPoly_injective
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_mul_rust,
    psiTower128ToPoly_polyToTower128, psiTower128ToPoly_polyToTower128]

theorem polyToTower128_mul (a b : BitVec 128) :
    polyToTower128 (gf2_128_mul_bv a b) = towerMul 7 (polyToTower128 a) (polyToTower128 b) := by
  rw [gf2_128_mul_bv_eq_rustGf128Mul, polyToTower128_mul_rust]

theorem polyToTower128_eq_zero_iff (a : BitVec 128) :
    polyToTower128 a = towerZero 7 ↔ a = 0#128 :=
  ⟨fun h => polyToTower128_injective a _ (h.trans polyToTower128_zero.symm),
   fun h => by rw [h, polyToTower128_zero]⟩

theorem psiTower128ToPoly_bijective : IsBijective psiTower128ToPoly :=
  ⟨psiTower128ToPoly_injective, fun b => ⟨polyToTower128 b, psiTower128ToPoly_polyToTower128 b⟩⟩

/-- **Field isomorphism `Tower128 ≅ GF(2)[x]/(x^128+x^7+x^2+x+1)` in Rust's coordinates.**
    Every conjunct quantifies over all field elements; none is a constant check. -/
theorem psiTower128ToPoly_field_isomorphism :
    psiTower128ToPoly (towerZero 7) = 0#128 ∧
    psiTower128ToPoly (towerOne 7) = 1#128 ∧
    (∀ a b : Tower128,
      psiTower128ToPoly (towerAdd 7 a b) = psiTower128ToPoly a ^^^ psiTower128ToPoly b) ∧
    (∀ a b : Tower128,
      psiTower128ToPoly (towerMul 7 a b) =
        rustGf128Mul (psiTower128ToPoly a) (psiTower128ToPoly b)) ∧
    (∀ t : Tower128, polyToTower128 (psiTower128ToPoly t) = t) ∧
    (∀ a : BitVec 128, psiTower128ToPoly (polyToTower128 a) = a) :=
  ⟨psiTower128ToPoly_zero, psiTower128ToPoly_one, psiTower128ToPoly_add,
   psiTower128ToPoly_mul_rust, polyToTower128_psiTower128ToPoly,
   psiTower128ToPoly_polyToTower128⟩


end Qsag


namespace Qsag

theorem towerZero_ne_towerOne (k : Nat) : towerZero k ≠ towerOne k :=
  fun h => towerOne_ne_zero k h.symm

theorem Math.towerInv_zero : ∀ k : Nat, towerInv k (towerZero k) = towerZero k
  | 0 => rfl
  | k + 1 => by
    unfold towerInv towerZero
    dsimp only
    rw [towerMul_zero, towerAdd_zero, towerZero_mul]

instance instLawfulFieldTowerElem (k : Nat) : LawfulField (TowerElem k) where
  inv := towerInv k
  zero_ne_one := towerZero_ne_towerOne k
  inv_zero := Math.towerInv_zero k
  mul_inv_cancel {_a} ha := towerMul_inv k _ ha

end Qsag

namespace Qsag.Math

set_option autoImplicit false

/-- Canonical polynomial-basis element of `𝔽_{2^{128}} = 𝔽_2[x]/(x^128 + x^7 + x^2 + x + 1)`. -/
structure Gf2Pow128 where
  bits : BitVec 128
  deriving DecidableEq, Repr

namespace Gf2Pow128

@[ext] theorem ext {a b : Gf2Pow128} (h : a.bits = b.bits) : a = b := by
  cases a; cases b; cases h; rfl

def zero : Gf2Pow128 := ⟨0#128⟩

def one : Gf2Pow128 := ⟨1#128⟩

def add (a b : Gf2Pow128) : Gf2Pow128 := ⟨a.bits ^^^ b.bits⟩

def mul (a b : Gf2Pow128) : Gf2Pow128 := ⟨Qsag.gf2_128_mul_bv a.bits b.bits⟩

theorem mul_bits (a b : Gf2Pow128) : (mul a b).bits = Qsag.gf2_128_mul_bv a.bits b.bits := by
  unfold mul
  rfl

def inv (a : Gf2Pow128) : Gf2Pow128 :=
  ⟨Qsag.psiTower128ToPoly (Qsag.towerInv 7 (Qsag.polyToTower128 a.bits))⟩

instance : Inhabited Gf2Pow128 := ⟨zero⟩

instance : CommRingOps Gf2Pow128 where
  zero := zero
  one := one
  add := add
  mul := mul
  neg a := a
  sub := add

private theorem toTower_inj {a b : Gf2Pow128}
    (h : Qsag.polyToTower128 a.bits = Qsag.polyToTower128 b.bits) : a = b :=
  ext (Qsag.polyToTower128_injective a.bits b.bits h)

private theorem toTower_add (a b : Gf2Pow128) :
    Qsag.polyToTower128 (CommRingOps.add a b).bits =
      Qsag.towerAdd 7 (Qsag.polyToTower128 a.bits) (Qsag.polyToTower128 b.bits) :=
  Qsag.polyToTower128_xor a.bits b.bits

private theorem toTower_mul (a b : Gf2Pow128) :
    Qsag.polyToTower128 (CommRingOps.mul a b).bits =
      Qsag.towerMul 7 (Qsag.polyToTower128 a.bits) (Qsag.polyToTower128 b.bits) :=
  Qsag.polyToTower128_mul a.bits b.bits

instance : LawfulCommRing Gf2Pow128 where
  add_assoc a b c := by
    apply toTower_inj
    rw [toTower_add, toTower_add, toTower_add, toTower_add]
    exact Qsag.towerAdd_assoc 7 _ _ _
  add_comm a b := by
    apply toTower_inj
    rw [toTower_add, toTower_add]
    exact Qsag.towerAdd_comm 7 _ _
  zero_add a := by
    apply toTower_inj
    rw [toTower_add, show (CommRingOps.zero : Gf2Pow128).bits = 0#128 from rfl, Qsag.polyToTower128_zero]
    exact Qsag.towerZero_add 7 _
  add_zero a := by
    apply toTower_inj
    rw [toTower_add, show (CommRingOps.zero : Gf2Pow128).bits = 0#128 from rfl, Qsag.polyToTower128_zero]
    exact Qsag.towerAdd_zero 7 _
  add_left_neg a := by
    apply toTower_inj
    change Qsag.polyToTower128 (CommRingOps.add a a).bits = Qsag.polyToTower128 (CommRingOps.zero : Gf2Pow128).bits
    rw [toTower_add, show (CommRingOps.zero : Gf2Pow128).bits = 0#128 from rfl, Qsag.polyToTower128_zero]
    exact Qsag.towerAdd_self_zero 7 _
  sub_eq_add_neg _ _ := rfl
  mul_comm a b := by
    apply toTower_inj
    rw [toTower_mul, toTower_mul]
    exact Qsag.towerMul_comm 7 _ _
  one_mul a := by
    apply toTower_inj
    rw [toTower_mul, show (CommRingOps.one : Gf2Pow128).bits = 1#128 from rfl, Qsag.polyToTower128_one]
    exact Qsag.towerOne_mul 7 _
  mul_one a := by
    apply toTower_inj
    rw [toTower_mul, show (CommRingOps.one : Gf2Pow128).bits = 1#128 from rfl, Qsag.polyToTower128_one]
    exact Qsag.towerMul_one 7 _
  left_distrib a b c := by
    apply toTower_inj
    rw [toTower_mul, toTower_add, toTower_add, toTower_mul, toTower_mul]
    exact Qsag.towerMul_add_distrib 7 _ _ _
  right_distrib a b c := by
    apply toTower_inj
    rw [toTower_mul, toTower_add, toTower_add, toTower_mul, toTower_mul]
    exact Qsag.towerAdd_mul_distrib 7 _ _ _
  mul_assoc a b c := by
    apply toTower_inj
    rw [toTower_mul, toTower_mul, toTower_mul, toTower_mul]
    exact Qsag.towerMul_assoc 7 _ _ _

theorem mul_inv_cancel {a : Gf2Pow128} (ha : a ≠ CommRingOps.zero) :
    CommRingOps.mul a (inv a) = CommRingOps.one := by
  apply toTower_inj
  rw [toTower_mul, show (CommRingOps.one : Gf2Pow128).bits = 1#128 from rfl]
  unfold inv
  dsimp only
  rw [Qsag.polyToTower128_psiTower128ToPoly, Qsag.polyToTower128_one]
  have hTowerNe : Qsag.polyToTower128 a.bits ≠ Qsag.towerZero 7 := by
    intro h0
    apply ha
    apply ext
    exact (Qsag.polyToTower128_eq_zero_iff a.bits).mp h0
  exact Qsag.towerMul_inv 7 _ hTowerNe

theorem zero_ne_one : (CommRingOps.zero : Gf2Pow128) ≠ CommRingOps.one := by
  intro h
  have hb : (0#128 : BitVec 128) = 1#128 := congrArg Gf2Pow128.bits h
  exact absurd hb (by decide)

theorem inv_zero : inv zero = zero := by
  unfold inv zero
  rw [Qsag.polyToTower128_zero, towerInv_zero 7, Qsag.psiTower128ToPoly_zero]

instance : LawfulField Gf2Pow128 where
  inv := inv
  zero_ne_one := zero_ne_one
  inv_zero := inv_zero
  mul_inv_cancel := mul_inv_cancel

instance : NoZeroDivisors Gf2Pow128 :=
  Qsag.LawfulField.toNoZeroDivisors Gf2Pow128

end Gf2Pow128

/-- Constructive ring isomorphism `Tower128 ≃+* Gf2Pow128`. -/
def ringIsoTower128ToPoly : RingIso Qsag.Tower128 Gf2Pow128 where
  toFun t := ⟨Qsag.psiTower128ToPoly t⟩
  invFun p := Qsag.polyToTower128 p.bits
  left_inv t := Qsag.polyToTower128_psiTower128ToPoly t
  right_inv p := Gf2Pow128.ext (Qsag.psiTower128ToPoly_polyToTower128 p.bits)
  map_zero := Gf2Pow128.ext Qsag.psiTower128ToPoly_zero
  map_one := Gf2Pow128.ext Qsag.psiTower128ToPoly_one
  map_add x y := Gf2Pow128.ext (Qsag.psiTower128ToPoly_add x y)
  map_neg _ := rfl
  map_sub x y := Gf2Pow128.ext (Qsag.psiTower128ToPoly_add x y)
  map_mul x y := Gf2Pow128.ext (Qsag.psiTower128ToPoly_mul x y)

theorem towerInv7_zero :
    LawfulField.inv (CommRingOps.zero : Qsag.Tower128) = CommRingOps.zero :=
  LawfulField.inv_zero

theorem gf2Pow128_inv_zero :
    LawfulField.inv (CommRingOps.zero : Gf2Pow128) = CommRingOps.zero :=
  LawfulField.inv_zero

/-- **Canonical Field Isomorphism (`isoTower128ToPoly : FieldIso Tower128 Gf2Pow128`)**:
    Preserves `0, 1, +, -, sub, *`, and `inv` across Wiedemann's tower and the polynomial basis. -/
@[expose] def isoTower128ToPoly : FieldIso Qsag.Tower128 Gf2Pow128 :=
  ringIsoTower128ToPoly.toFieldIso


end Qsag.Math

namespace Qsag
/-- Certified basis images and nondegenerate product for the deployed two-lane
linear map. The arithmetic is checked in the field module; users consume these
three equations without opening the basis conversion implementation. -/
theorem gf128_linear_layer_basis_certificate :
    psiTower128ToPoly (unpackTower 7 0x6938822d2669c41b597c42deeb84a0bb#128) =
      0x9E3779B97F4A7C15F39CC0605CEDC835#128 ∧
    psiTower128ToPoly (unpackTower 7 0x2df5aeeede6d3f143c5406b243efb482#128) =
      0xBF58476D1CE4E5B994D049BB133111EB#128 ∧
    gf2_128_mul_bv 0x9E3779B97F4A7C15F39CC0605CEDC835#128
      0xBF58476D1CE4E5B994D049BB133111EB#128 ≠ 1#128 := by
  decide

/-! ### Exports for lane cred-mig -/

/-- `X · X^j = X^(j+1)` below the reduction degree. -/
theorem MigrationExecution.rustGf128MulX_twoPow_succ (j : Nat) (hj : j < 127) :
    MigrationExecution.rustGf128MulX (BitVec.twoPow 128 j) = BitVec.twoPow 128 (j + 1) :=
  MigrationExecution.rustGf128MulX_twoPow j hj
end Qsag

namespace Qsag
/-- Public unfolding of `joinBits` (its compiler equation mentions a private proof). -/
theorem joinBits_eq_append (k : Nat) (lo hi : TowerBitVec k) :
    joinBits k lo hi = (hi ++ lo).cast (Nat.two_pow_succ k).symm := by
  unfold joinBits; rfl
/-- Executed values of the Rust multiplication behind `rust_spn_poly_basis_kats` (`Oracle/Spn`): the
`pow7_plain` product tree `(x·x²)·(x²·x²)` at `2` and `3`, and both lanes of one round body at state
`(3, 5)`, round constant `(7, 11)`, with the two deployed linear-layer constants. Checked here because
the multiplication loop is not exported. -/
theorem rustGf128Mul_pow7_round_kats :
    MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul 2#128 (MigrationExecution.rustGf128Mul 2#128 2#128)) (MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul 2#128 2#128) (MigrationExecution.rustGf128Mul 2#128 2#128)) = 0x80#128 ∧
    MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul 3#128 (MigrationExecution.rustGf128Mul 3#128 3#128)) (MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul 3#128 3#128) (MigrationExecution.rustGf128Mul 3#128 3#128)) = 0xff#128 ∧
    (MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul (3#128 ^^^ 7#128) (MigrationExecution.rustGf128Mul (3#128 ^^^ 7#128) (3#128 ^^^ 7#128))) (MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul (3#128 ^^^ 7#128) (3#128 ^^^ 7#128)) (MigrationExecution.rustGf128Mul (3#128 ^^^ 7#128) (3#128 ^^^ 7#128)))) ^^^
        MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul (5#128 ^^^ 11#128) (MigrationExecution.rustGf128Mul (5#128 ^^^ 11#128) (5#128 ^^^ 11#128))) (MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul (5#128 ^^^ 11#128) (5#128 ^^^ 11#128)) (MigrationExecution.rustGf128Mul (5#128 ^^^ 11#128) (5#128 ^^^ 11#128)))) 0x9E3779B97F4A7C15F39CC0605CEDC835#128 =
      0x7e449a0c3042bf1c84c9783f54d336e9#128 ∧
    (MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul (5#128 ^^^ 11#128) (MigrationExecution.rustGf128Mul (5#128 ^^^ 11#128) (5#128 ^^^ 11#128))) (MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul (5#128 ^^^ 11#128) (5#128 ^^^ 11#128)) (MigrationExecution.rustGf128Mul (5#128 ^^^ 11#128) (5#128 ^^^ 11#128)))) ^^^
        MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul (3#128 ^^^ 7#128) (MigrationExecution.rustGf128Mul (3#128 ^^^ 7#128) (3#128 ^^^ 7#128))) (MigrationExecution.rustGf128Mul (MigrationExecution.rustGf128Mul (3#128 ^^^ 7#128) (3#128 ^^^ 7#128)) (MigrationExecution.rustGf128Mul (3#128 ^^^ 7#128) (3#128 ^^^ 7#128)))) 0xBF58476D1CE4E5B994D049BB133111EB#128 =
      0x11db4739396e6534126ec4cc445b09a2#128 := by
  decide +kernel
/-- Reading the tower word of `GF128_MDS_A` through `towerToRust` (the wrong basis map) does not give
its polynomial-basis image; the executed half of `towerToRust_differs_from_psi_on_mds_constant`
(`Oracle/Spn`). -/
theorem gf128_towerToRust_mds_a_ne_poly_bits :
    MigrationExecution.towerToRust 7 (unpackTower 7 0x6938822d2669c41b597c42deeb84a0bb#128) ≠
      0x9E3779B97F4A7C15F39CC0605CEDC835#128 := by
  decide +kernel
#verify_constructive Qsag.rustGf128Mul_pow7_round_kats Qsag.gf128_towerToRust_mds_a_ne_poly_bits
#export_eqns lowBits highBits Simulates rustGf128MulXIter
#export_eqns MigrationExecution.rustGf128MulX MigrationExecution.rustGf128MulLoop MigrationExecution.rustGf128Mul MigrationExecution.rustPolyAct
end Qsag

/-! ## Executed controls for `Tests/MathAndCoding`

Kernel-evaluated witnesses and teeth, stated here because the definitions they execute are sealed outside
this module. `Tests/MathAndCoding` audits and pairs them. -/
public section
namespace Qsag.MigrationExecution

set_option autoImplicit false
set_option exponentiation.threshold 512
set_option maxRecDepth 4096 in
theorem rust_gf128_basis_kats :
    rustGf128Mul 2#128 2#128 = 4#128 ∧
    rustGf128Mul (BitVec.ofNat 128 (2^127)) 2#128 = 0x87#128 ∧
    rustGf128OfLimbs 0 1 = BitVec.ofNat 128 (2^64) := by
  decide +kernel

/-- Regression against treating Wiedemann coordinate bit-packing as the Rust polynomial basis
    (the verified conversion is `rustToTower`):
    under naive coordinate bit-packing, bit `1` (`x_0 ∈ Tower128`) squares to `x_0 + 1` (`3#128`),
    whereas in `RustGf128` bit `1` (`x`) squares to `x^2` (`4#128`). -/
theorem tooth_identity_basis_conversion_wrong :
    ∃ x : RustGf128,
      rustGf128Mul x x ≠
        wiedemannPack128 (towerMul 7 (wiedemannUnpack128 x) (wiedemannUnpack128 x)) ∧
      wiedemannUnpack128 (rustGf128Mul x x) ≠
        towerMul 7 (wiedemannUnpack128 x) (wiedemannUnpack128 x) := by
  refine ⟨2#128, ?_⟩
  have hK : towerMul 7 (wiedemannUnpack128 2#128) (wiedemannUnpack128 2#128) =
      wiedemannKaratsuba 7 (wiedemannUnpack128 2#128) (wiedemannUnpack128 2#128) :=
    (wiedemannKaratsuba_eq_towerMul 7 _ _).symm
  have hW : wiedemannPack128 (wiedemannKaratsuba 7 (wiedemannUnpack128 2#128) (wiedemannUnpack128 2#128)) = 3#128 := by
    decide
  have hR : rustGf128Mul 2#128 2#128 = 4#128 := by decide +kernel
  rw [hK]
  refine ⟨?_, ?_⟩
  · rw [hR, hW]; decide
  · intro hEq
    have hp := congrArg wiedemannPack128 hEq
    rw [hW] at hp
    have h4 : wiedemannPack128 (wiedemannUnpack128 (rustGf128Mul 2#128 2#128)) = 4#128 := by
      rw [hR]; decide
    rw [h4] at hp
    revert hp; decide

-- (math-teeth anchor MigrationExecution )
end Qsag.MigrationExecution
end
#verify_constructive
  Qsag.MigrationExecution.rust_gf128_basis_kats
  Qsag.MigrationExecution.tooth_identity_basis_conversion_wrong

/-! ## Executed controls for `Tests/MathAndCoding`

Kernel-evaluated witnesses and teeth, stated here because the definitions they execute are sealed outside
this module. `Tests/MathAndCoding` audits and pairs them. -/
public section
namespace Qsag
open MigrationExecution
set_option autoImplicit false
set_option exponentiation.threshold 512
theorem tooth_packTower_is_not_the_poly_basis :
    psiTower128ToPoly (unpackTower 7 2#128) ≠ 2#128 ∧
    mulExec 7 2#128 2#128 = 3#128 ∧ rustGf128Mul 2#128 2#128 = 4#128 := by
  refine ⟨?_, ?_, rust_gf128_basis_kats.1⟩
  · have h : psiTower128ToPoly (unpackTower 7 2#128) =
        0x295ac0b1f4731af9676aac9fa4b20b08#128 := by decide +kernel
    rw [h]; decide
  · decide +kernel

-- (math-teeth anchor Qsag MigrationExecution)
end Qsag
end
#verify_constructive
  Qsag.tooth_packTower_is_not_the_poly_basis

-- Owning-module audit certificates for the theorems audited again in `Tests/MigrationTeeth`.
#verify_constructive
  Qsag.MigrationExecution.rustToTower_mul
  Qsag.MigrationExecution.rustGf128Mul_comm
  Qsag.MigrationExecution.rustGf128Mul_assoc
  Qsag.MigrationExecution.towerToRust_mul
  Qsag.MigrationExecution.towerToRust_injective
  Qsag.MigrationExecution.towerToRust_rustToTower
  Qsag.MigrationExecution.rustToTower_towerToRust
  Qsag.MigrationExecution.rustGf128Mul_eq_zero

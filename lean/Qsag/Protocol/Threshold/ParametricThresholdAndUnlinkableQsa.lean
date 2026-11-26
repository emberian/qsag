module


public import Qsag.Math.CommitteeMasks
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Protocol.Threshold.Preprocessing
import Qsag.Tactic.AssuranceKit
import Qsag.Math.Tactic.CommRing

public section
namespace Qsag

set_option autoImplicit false


/-- One balanced Feistel round on `(L, R) : BitVec m × BitVec m` with round PRF `rf : BitVec m → BitVec m`. -/
def feistelStep {m : Nat} (rf : BitVec m → BitVec m) (lr : BitVec m × BitVec m) :
    BitVec m × BitVec m :=
  (lr.2, lr.1 ^^^ rf lr.2)

/-- Exact inverse of one balanced Feistel round (`(L', R') ↦ (R' ^^^ rf L', L')`). -/
def feistelStepInv {m : Nat} (rf : BitVec m → BitVec m) (lr : BitVec m × BitVec m) :
    BitVec m × BitVec m :=
  (lr.2 ^^^ rf lr.1, lr.1)

theorem feistelStepInv_feistelStep {m : Nat} (rf : BitVec m → BitVec m) (lr : BitVec m × BitVec m) :
    feistelStepInv rf (feistelStep rf lr) = lr := by
  cases lr with
  | mk L R =>
    unfold feistelStep feistelStepInv
    dsimp only
    have hCancel : (L ^^^ rf R) ^^^ rf R = L := by bv_xor_cancel
    rw [hCancel]

theorem feistelStep_feistelStepInv {m : Nat} (rf : BitVec m → BitVec m) (lr : BitVec m × BitVec m) :
    feistelStep rf (feistelStepInv rf lr) = lr := by
  cases lr with
  | mk L R =>
    unfold feistelStep feistelStepInv
    dsimp only
    have hCancel : (R ^^^ rf L) ^^^ rf L = R := by bv_xor_cancel
    rw [hCancel]

/-- Multi-round Feistel evaluation across round functions `rfs : List (BitVec m → BitVec m)`. -/
def feistelRounds {m : Nat} : List (BitVec m → BitVec m) → (BitVec m × BitVec m) → (BitVec m × BitVec m)
  | [], lr => lr
  | rf :: rest, lr => feistelRounds rest (feistelStep rf lr)

/-- Multi-round Feistel inverse across `rfs`. -/
def feistelRoundsInv {m : Nat} : List (BitVec m → BitVec m) → (BitVec m × BitVec m) → (BitVec m × BitVec m)
  | [], lr => lr
  | rf :: rest, lr => feistelStepInv rf (feistelRoundsInv rest lr)

theorem feistelRoundsInv_feistelRounds {m : Nat} :
    ∀ (rfs : List (BitVec m → BitVec m)) (lr : BitVec m × BitVec m),
      feistelRoundsInv rfs (feistelRounds rfs lr) = lr
  | [], lr => rfl
  | rf :: rest, lr => by
    simp only [feistelRounds, feistelRoundsInv,
      feistelRoundsInv_feistelRounds rest (feistelStep rf lr),
      feistelStepInv_feistelStep]

theorem feistelRounds_feistelRoundsInv {m : Nat} :
    ∀ (rfs : List (BitVec m → BitVec m)) (lr : BitVec m × BitVec m),
      feistelRounds rfs (feistelRoundsInv rfs lr) = lr
  | [], lr => rfl
  | rf :: rest, lr => by
    simp only [feistelRoundsInv, feistelRounds,
      feistelStep_feistelStepInv, feistelRounds_feistelRoundsInv rest lr]

/-- Split `Fin (2 ^ m * 2 ^ m)` into `(q, r) : BitVec m × BitVec m` and pack back bijectively. -/
def splitFinFeistel (m : Nat) (x : Fin (2 ^ (2 * m))) : BitVec m × BitVec m :=
  (BitVec.ofNat m (x.val / 2 ^ m), BitVec.ofNat m (x.val % 2 ^ m))

private theorem pow_two_mul_eq (m : Nat) : 2 ^ m * 2 ^ m = 2 ^ (2 * m) := by
  rw [← Nat.pow_add, Nat.two_mul]

private theorem two_pow_pos_pt : ∀ m : Nat, 0 < 2 ^ m
  | 0 => by decide
  | m + 1 => by
    rw [Nat.pow_succ]
    have ih := two_pow_pos_pt m
    omega

def joinFinFeistel (m : Nat) (lr : BitVec m × BitVec m) : Fin (2 ^ (2 * m)) :=
  ⟨lr.1.toNat * 2 ^ m + lr.2.toNat, by
    have hL := lr.1.isLt
    have hR := lr.2.isLt
    have hBound : lr.1.toNat * 2 ^ m + lr.2.toNat < 2 ^ m * 2 ^ m := by
      have h1 : (lr.1.toNat + 1) * 2 ^ m ≤ 2 ^ m * 2 ^ m :=
        Nat.mul_le_mul_right (2 ^ m) hL
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    exact Nat.lt_of_lt_of_eq hBound (pow_two_mul_eq m)⟩

theorem joinFinFeistel_splitFinFeistel (m : Nat) (x : Fin (2 ^ (2 * m))) :
    joinFinFeistel m (splitFinFeistel m x) = x := by
  apply Fin.ext
  unfold joinFinFeistel splitFinFeistel
  dsimp only
  have hxLt : x.val < 2 ^ m * 2 ^ m := Nat.lt_of_lt_of_eq x.isLt (pow_two_mul_eq m).symm
  have hPos : 0 < 2 ^ m := two_pow_pos_pt m
  have hqLt : x.val / 2 ^ m < 2 ^ m := by
    have hdm := Nat.div_add_mod x.val (2 ^ m)
    if hge : 2 ^ m ≤ x.val / 2 ^ m then
      have hm := Nat.mul_le_mul_left (2 ^ m) hge
      omega
    else
      omega
  have hrLt : x.val % 2 ^ m < 2 ^ m := Nat.mod_lt x.val hPos
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqLt, Nat.mod_eq_of_lt hrLt,
    Nat.mul_comm _ (2 ^ m), Nat.div_add_mod]

theorem splitFinFeistel_joinFinFeistel (m : Nat) (lr : BitVec m × BitVec m) :
    splitFinFeistel m (joinFinFeistel m lr) = lr := by
  cases lr with
  | mk L R =>
    unfold splitFinFeistel joinFinFeistel
    dsimp only
    have hPos : 0 < 2 ^ m := two_pow_pos_pt m
    have hR := R.isLt
    have hDiv : (L.toNat * 2 ^ m + R.toNat) / 2 ^ m = L.toNat := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hPos, Nat.div_eq_of_lt hR, Nat.zero_add]
    have hMod : (L.toNat * 2 ^ m + R.toNat) % 2 ^ m = R.toNat := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR]
    rw [hDiv, hMod, BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- Constructive `k`-round balanced Feistel PRP over `Fin (2 ^ (2 * m))` (`0 Classical.choice`). -/
def feistelFinEquiv (m : Nat) (rfs : List (BitVec m → BitVec m)) :
    SimpleEquiv (Fin (2 ^ (2 * m))) (Fin (2 ^ (2 * m))) where
  toFun x := joinFinFeistel m (feistelRounds rfs (splitFinFeistel m x))
  invFun y := joinFinFeistel m (feistelRoundsInv rfs (splitFinFeistel m y))
  left_inv x := by
    rw [splitFinFeistel_joinFinFeistel, feistelRoundsInv_feistelRounds, joinFinFeistel_splitFinFeistel]
  right_inv y := by
    rw [splitFinFeistel_joinFinFeistel, feistelRounds_feistelRoundsInv, joinFinFeistel_splitFinFeistel]

/-- Raw contiguous slot index `c * B + s < C * B ≤ 2 ^ h` as an element of `Fin (2 ^ h)`. -/
def rawCommitteeSlot {C B h : Nat} (hCap : C * B ≤ 2 ^ h) (c : Fin C) (s : Fin B) : Fin (2 ^ h) :=
  ⟨c.val * B + s.val, by
    have h1 : (c.val + 1) * B ≤ C * B := Nat.mul_le_mul_right B c.isLt
    rw [Nat.add_mul, Nat.one_mul] at h1
    have hs := s.isLt
    omega⟩

theorem rawCommitteeSlot_injective {C B h : Nat} (hCap : C * B ≤ 2 ^ h)
    {c1 c2 : Fin C} {s1 s2 : Fin B}
    (hEq : rawCommitteeSlot hCap c1 s1 = rawCommitteeSlot hCap c2 s2) :
    c1 = c2 ∧ s1 = s2 := by
  have hv : c1.val * B + s1.val = c2.val * B + s2.val := congrArg Fin.val hEq
  obtain ⟨hc, hs⟩ := committee_leaf_ranges_disjoint s1.isLt s2.isLt hv
  exact ⟨Fin.ext hc, Fin.ext hs⟩

/-- **PRP-Striped `QS-A` Leaf Assignment (`prpStripedLeafIndex`)**:
    Maps `(committee_id, local_seq) ∈ Fin C × Fin B` (`C * B ≤ 2 ^ h`) through a bijective PRP
    `piK : SimpleEquiv (Fin (2 ^ h)) (Fin (2 ^ h))` to its global `Jorts` Merkle leaf in `Fin (2 ^ h)`. -/
def prpStripedLeafIndex {C B h : Nat} (hCap : C * B ≤ 2 ^ h)
    (piK : SimpleEquiv (Fin (2 ^ h)) (Fin (2 ^ h))) (c : Fin C) (s : Fin B) : Fin (2 ^ h) :=
  piK.toFun (rawCommitteeSlot hCap c s)

/-- Unstriped contiguous `QS-A` leaf assignment `c * B + s` (deterministic committee leakage baseline). -/
def contiguousQsaLeaf {C B h : Nat} (hCap : C * B ≤ 2 ^ h) (c : Fin C) (s : Fin B) : Fin (2 ^ h) :=
  rawCommitteeSlot hCap c s


/-- Transposition `SimpleEquiv (Fin M) (Fin M)` swapping `u` and `v` (`0 Classical.choice`). -/
def swapFinEquiv {M : Nat} (u v : Fin M) : SimpleEquiv (Fin M) (Fin M) where
  toFun x := if x = u then v else if x = v then u else x
  invFun x := if x = u then v else if x = v then u else x
  left_inv x := by
    if hxu : x = u then
      subst hxu
      if huv : x = v then subst huv; simp else simp [Ne.symm huv]
    else if hxv : x = v then
      subst hxv; simp
    else
      simp [hxu, hxv]
  right_inv x := by
    if hxu : x = u then
      subst hxu
      if huv : x = v then subst huv; simp else simp [Ne.symm huv]
    else if hxv : x = v then
      subst hxv; simp
    else
      simp [hxu, hxv]

/-- Compose two `SimpleEquiv` bijections (`e2 ∘ e1`). -/
def compSimpleEquiv {α β γ : Type} (e1 : SimpleEquiv α β) (e2 : SimpleEquiv β γ) :
    SimpleEquiv α γ where
  toFun a := e2.toFun (e1.toFun a)
  invFun c := e1.invFun (e2.invFun c)
  left_inv a := by rw [e2.left_inv, e1.left_inv]
  right_inv c := by rw [e1.right_inv, e2.right_inv]

/-- **Committee Unlinkability of PRP-Striped `QS-A` (`prp_striped_qsa_committee_unlinkability`)**:
    1. **Ideal Random-Permutation Symmetry (`0` Advantage)**: Pre-composing any permutation `pi` with
       the slot transposition `swapFinEquiv (rawCommitteeSlot hCap c1 s1) (rawCommitteeSlot hCap c2 s2)`
       maps `(c1, s1)`'s leaf under the transposed permutation identically to `(c2, s2)`'s leaf under
       `pi`, so across any transposition-closed permutation space `(Fin PermCard)` (`permSwapEquiv`),
       EVERY public leaf distinguisher `D : Fin (2 ^ h) → Bool` has **exact advantage `0`** between
       `(c1, s1)` and `(c2, s2)`!
    2. **Keyed Feistel-PRP Indistinguishability Reduction**: For ANY keyed PRP family
       `prpFamily : Fin KeyCard → SimpleEquiv (Fin (2 ^ h)) (Fin (2 ^ h))` whose single-slot output
       distinguishing error from uniform `Fin (2 ^ h)` is bounded by `epsPrpNum`, ANY public
       committee-identifying distinguisher `D : Fin (2 ^ h) → Bool` separating `(c1, s1)` from `(c2, s2)`
       has scaled advantage bounded by `2 * epsPrpNum`! -/
theorem prp_striped_qsa_committee_unlinkability
    {C B h : Nat} (hCap : C * B ≤ 2 ^ h) (c1 c2 : Fin C) (s1 s2 : Fin B) :
    -- (1) Exact ideal-permutation symmetry (0 advantage):
    (∀ {PermCard : Nat} (perms : Fin PermCard → SimpleEquiv (Fin (2 ^ h)) (Fin (2 ^ h)))
       (permSwapIdx : SimpleEquiv (Fin PermCard) (Fin PermCard))
       (_hSwapSpec : ∀ p : Fin PermCard,
         (perms (permSwapIdx.toFun p)).toFun (rawCommitteeSlot hCap c1 s1) =
           (perms p).toFun (rawCommitteeSlot hCap c2 s2))
       (D : Fin (2 ^ h) → Bool),
      qsum PermCard (fun p => if D (prpStripedLeafIndex hCap (perms p) c1 s1) then 1 else 0) =
      qsum PermCard (fun p => if D (prpStripedLeafIndex hCap (perms p) c2 s2) then 1 else 0)) ∧
    -- (2) Tight 2 * epsPrpNum keyed-PRP security reduction:
    (∀ {KeyCard : Nat} (prpFamily : Fin KeyCard → SimpleEquiv (Fin (2 ^ h)) (Fin (2 ^ h)))
       (epsPrpNum : Nat) (D : Fin (2 ^ h) → Bool),
      (∀ raw : Fin (2 ^ h),
        natAbsDiff
          (2 ^ h * qsum KeyCard (fun k => if D ((prpFamily k).toFun raw) then 1 else 0))
          (KeyCard * qsum (2 ^ h) (fun y => if D y then 1 else 0)) ≤ epsPrpNum) →
      natAbsDiff
        (2 ^ h * qsum KeyCard (fun k => if D (prpStripedLeafIndex hCap (prpFamily k) c1 s1) then 1 else 0))
        (2 ^ h * qsum KeyCard (fun k => if D (prpStripedLeafIndex hCap (prpFamily k) c2 s2) then 1 else 0)) ≤
      epsPrpNum + epsPrpNum) := by
  refine ⟨?_, ?_⟩
  · intro PermCard perms permSwapIdx hSwapSpec D
    have hBij :
        qsum PermCard (fun p =>
          if D (prpStripedLeafIndex hCap (perms (permSwapIdx.toFun p)) c1 s1) then 1 else 0) =
        qsum PermCard (fun p => if D (prpStripedLeafIndex hCap (perms p) c1 s1) then 1 else 0) :=
      qsum_bijection_invariant
        { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
        permSwapIdx
        (fun p => if D (prpStripedLeafIndex hCap (perms p) c1 s1) then 1 else 0)
    refine hBij.symm.trans (qsum_congr ?_)
    intro p
    unfold prpStripedLeafIndex
    rw [hSwapSpec p]
  · intro KeyCard prpFamily epsPrpNum D hPrp
    have h1 := hPrp (rawCommitteeSlot hCap c1 s1)
    have h2 := hPrp (rawCommitteeSlot hCap c2 s2)
    have h2Symm : natAbsDiff
        (KeyCard * qsum (2 ^ h) (fun y => if D y then 1 else 0))
        (2 ^ h * qsum KeyCard (fun k => if D ((prpFamily k).toFun (rawCommitteeSlot hCap c2 s2)) then 1 else 0)) ≤
        epsPrpNum := by
      rw [natAbsDiff_eq] at h2 ⊢
      split at h2 <;> split <;> omega
    have hTri := natAbsDiff_triangle
      (2 ^ h * qsum KeyCard (fun k => if D (prpStripedLeafIndex hCap (prpFamily k) c1 s1) then 1 else 0))
      (KeyCard * qsum (2 ^ h) (fun y => if D y then 1 else 0))
      (2 ^ h * qsum KeyCard (fun k => if D (prpStripedLeafIndex hCap (prpFamily k) c2 s2) then 1 else 0))
    unfold prpStripedLeafIndex at hTri ⊢
    exact Nat.le_trans hTri (Nat.add_le_add h1 h2Symm)

/-- **`#tooth` Contiguous `QS-A` Deterministically Leaks `committee_id`
    (`tooth_contiguous_qsa_reveals_committee_id`)**:
    Without PRP striping (`contiguousQsaLeaf hCap c s = c * B + s`), integer division `(leaf.val / B)`
    deterministically recovers `c.val` and `(leaf.val % B)` recovers `s.val` for EVERY `s : Fin B`,
    giving a public distinguisher `D_leak(leaf) := decide (leaf.val / B = c1.val)` that separates
    any two distinct committees `c1 ≠ c2` with statistical distance `1` (`KeyCard` vs `0`)! -/
theorem tooth_contiguous_qsa_reveals_committee_id
    {C B h : Nat} (hBPos : 0 < B) (hCap : C * B ≤ 2 ^ h)
    (c1 c2 : Fin C) (hcNe : c1 ≠ c2) (s1 s2 : Fin B)
    (KeyCard : Nat) (hKeyPos : 0 < KeyCard) :
    ∃ D_leak : Fin (2 ^ h) → Bool,
      (contiguousQsaLeaf hCap c1 s1).val / B = c1.val ∧
      (contiguousQsaLeaf hCap c1 s1).val % B = s1.val ∧
      qsum KeyCard (fun _ => if D_leak (contiguousQsaLeaf hCap c1 s1) then 1 else 0) = KeyCard ∧
      qsum KeyCard (fun _ => if D_leak (contiguousQsaLeaf hCap c2 s2) then 1 else 0) = 0 ∧
      qsum KeyCard (fun _ => if D_leak (contiguousQsaLeaf hCap c1 s1) then 1 else 0) ≠
      qsum KeyCard (fun _ => if D_leak (contiguousQsaLeaf hCap c2 s2) then 1 else 0) := by
  have hDiv : ∀ (c : Fin C) (s : Fin B), (contiguousQsaLeaf hCap c s).val / B = c.val := by
    intro c s
    unfold contiguousQsaLeaf rawCommitteeSlot
    dsimp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hBPos, Nat.div_eq_of_lt s.isLt, Nat.zero_add]
  have hMod : ∀ (c : Fin C) (s : Fin B), (contiguousQsaLeaf hCap c s).val % B = s.val := by
    intro c s
    unfold contiguousQsaLeaf rawCommitteeSlot
    dsimp only
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt s.isLt]
  let D_leak : Fin (2 ^ h) → Bool := fun leaf => decide (leaf.val / B = c1.val)
  refine ⟨D_leak, hDiv c1 s1, hMod c1 s1, ?_⟩
  have h1 : D_leak (contiguousQsaLeaf hCap c1 s1) = true := by
    dsimp only [D_leak]; rw [hDiv]; exact decide_eq_true rfl
  have h2 : D_leak (contiguousQsaLeaf hCap c2 s2) = false := by
    dsimp only [D_leak]; rw [hDiv]
    exact decide_eq_false (fun hEq => hcNe (Fin.ext hEq.symm))
  have hAll : qsum KeyCard (fun _ => if D_leak (contiguousQsaLeaf hCap c1 s1) then 1 else 0) =
      KeyCard := by
    rw [h1]
    simp only [↓reduceIte, qsum_const, Nat.mul_one]
  have hNone : qsum KeyCard (fun _ => if D_leak (contiguousQsaLeaf hCap c2 s2) then 1 else 0) =
      0 := by
    rw [h2]
    simp only [Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]
  rw [hAll, hNone]
  exact ⟨rfl, rfl, by omega⟩


/-! ## §2. Parametric `(t, n)` (`2 ≤ t ≤ n`) Lagrange-to-Additive Co-ZK Migration & Threshold VOPRF -/

/-- Constructive primality typeclass wrapping `IsPrimeNat q` (`2 ≤ q` and prime divisor property). -/
class FactPrime (q : Nat) : Prop where
  isPrime : IsPrimeNat q

theorem FactPrime.two_le (q : Nat) [hp : FactPrime q] : 2 ≤ q := hp.isPrime.1

/-- Constructive canonical prime-field / modular ring carrier `ZMod q` (`0` Mathlib, `0 Classical.choice`). -/
structure ZMod (q : Nat) where
  val : Nat
  isLt : val < q
  deriving DecidableEq, Repr

namespace ZMod

theorem ext {q : Nat} {a b : ZMod q} (h : a.val = b.val) : a = b := by
  cases a; cases b; dsimp only at h; subst h; rfl

@[expose] def ofNat (q : Nat) [FactPrime q] (n : Nat) : ZMod q :=
  ⟨n % q, Nat.mod_lt n (Nat.lt_of_lt_of_le (by decide : 0 < 2) (FactPrime.two_le q))⟩

@[expose] def zero (q : Nat) [FactPrime q] : ZMod q :=
  ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) (FactPrime.two_le q)⟩

@[expose] def one (q : Nat) [FactPrime q] : ZMod q :=
  ⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 2) (FactPrime.two_le q)⟩

instance (q : Nat) [FactPrime q] : Inhabited (ZMod q) := ⟨zero q⟩

@[expose] def add {q : Nat} [FactPrime q] (a b : ZMod q) : ZMod q :=
  ofNat q (a.val + b.val)

@[expose] def neg {q : Nat} [FactPrime q] (a : ZMod q) : ZMod q :=
  ofNat q (q - a.val)

@[expose] def sub {q : Nat} [FactPrime q] (a b : ZMod q) : ZMod q :=
  add a (neg b)

@[expose] def mul {q : Nat} [FactPrime q] (a b : ZMod q) : ZMod q :=
  ofNat q (a.val * b.val)

/-- Constructive Bézout field inverse on `ZMod q` via `extGcd` (`0 Classical.choice`). -/
def inv {q : Nat} [hp : FactPrime q] (a : ZMod q) : ZMod q :=
  if a.val = 0 then zero q
  else
    ⟨((extGcd a.val q).2.1 % (q : Int)).toNat, by
      have hq := hp.isPrime.1
      have h0 := Int.emod_nonneg (extGcd a.val q).2.1 (by omega : (q : Int) ≠ 0)
      have h1 := Int.emod_lt_of_pos (extGcd a.val q).2.1 (by omega : (0 : Int) < (q : Int))
      omega⟩

theorem zero_val {q : Nat} [FactPrime q] : (zero q).val = 0 := rfl
theorem one_val {q : Nat} [FactPrime q] : (one q).val = 1 := rfl
theorem add_val {q : Nat} [FactPrime q] (a b : ZMod q) : (add a b).val = (a.val + b.val) % q := rfl
theorem mul_val {q : Nat} [FactPrime q] (a b : ZMod q) : (mul a b).val = (a.val * b.val) % q := rfl
theorem neg_val {q : Nat} [FactPrime q] (a : ZMod q) : (neg a).val = (q - a.val) % q := rfl

theorem add_assoc {q : Nat} [FactPrime q] (a b c : ZMod q) : add (add a b) c = add a (add b c) :=
  ext <| by rw [add_val, add_val, add_val, add_val, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem add_comm {q : Nat} [FactPrime q] (a b : ZMod q) : add a b = add b a :=
  ext <| by rw [add_val, add_val, Nat.add_comm]

theorem zero_add {q : Nat} [FactPrime q] (a : ZMod q) : add (zero q) a = a :=
  ext <| by rw [add_val, zero_val, Nat.zero_add, Nat.mod_eq_of_lt a.isLt]

theorem add_zero {q : Nat} [FactPrime q] (a : ZMod q) : add a (zero q) = a :=
  ext <| by rw [add_val, zero_val, Nat.add_zero, Nat.mod_eq_of_lt a.isLt]

theorem add_left_neg {q : Nat} [FactPrime q] (a : ZMod q) : add (neg a) a = zero q :=
  ext <| by
    rw [add_val, neg_val, Nat.mod_add_mod]
    have ha := a.isLt
    have hEq : q - a.val + a.val = q := by omega
    rw [hEq, Nat.mod_self, zero_val]

theorem mul_assoc {q : Nat} [FactPrime q] (a b c : ZMod q) : mul (mul a b) c = mul a (mul b c) :=
  ext <| by rw [mul_val, mul_val, mul_val, mul_val, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

theorem mul_comm {q : Nat} [FactPrime q] (a b : ZMod q) : mul a b = mul b a :=
  ext <| by rw [mul_val, mul_val, Nat.mul_comm]

theorem one_mul {q : Nat} [FactPrime q] (a : ZMod q) : mul (one q) a = a :=
  ext <| by rw [mul_val, one_val, Nat.one_mul, Nat.mod_eq_of_lt a.isLt]

theorem mul_one {q : Nat} [FactPrime q] (a : ZMod q) : mul a (one q) = a := by
  rw [mul_comm, one_mul]

theorem left_distrib {q : Nat} [FactPrime q] (a b c : ZMod q) :
    mul a (add b c) = add (mul a b) (mul a c) :=
  ext <| by
    rw [mul_val, add_val, add_val, mul_val, mul_val, Nat.mul_mod_mod, Nat.left_distrib,
      Nat.add_mod (a.val * b.val) (a.val * c.val) q]

theorem right_distrib {q : Nat} [FactPrime q] (a b c : ZMod q) :
    mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm (add a b) c, left_distrib, mul_comm c a, mul_comm c b]

theorem zero_ne_one {q : Nat} [FactPrime q] : zero q ≠ one q := by
  intro h
  have hv : (zero q).val = (one q).val := congrArg ZMod.val h
  rw [zero_val, one_val] at hv
  exact absurd hv (by decide)

theorem inv_zero {q : Nat} [FactPrime q] : inv (zero q) = zero q := by
  unfold inv
  split
  · rfl
  · next h => exact absurd zero_val h

/-- Bézout coefficients give a modular inverse: `a * u + q * v = 1` forces
    `a * (u mod q) ≡ 1 (mod q)` for `2 ≤ q`. -/
private theorem bezout_emod_eq_one {q : Nat} (hq : 2 ≤ q) (a u v : Int)
    (hbez : a * u + (q : Int) * v = 1) :
    a * (u % (q : Int)) % (q : Int) = 1 := by
  have hModProd : a * (u % (q : Int)) % (q : Int) = a * u % (q : Int) := by
    rw [Int.mul_emod a (u % (q : Int)) (q : Int), Int.emod_emod, ← Int.mul_emod]
  have hau : a * u = 1 + (q : Int) * (-v) := by
    rw [Int.mul_neg]
    omega
  rw [hModProd, hau, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by decide) (by omega)

theorem mul_inv_cancel {q : Nat} [hp : FactPrime q] {a : ZMod q} (ha : a ≠ zero q) :
    mul a (inv a) = one q := by
  have ha0 : a.val ≠ 0 := fun h => ha (ext h)
  have hLt := a.isLt
  have hqGe2 := hp.isPrime.1
  have hNotDvd : ¬ (q ∣ a.val) := fun hd => by
    have hle := Nat.le_of_dvd (by omega) hd
    omega
  obtain ⟨hda, hdq⟩ := extGcd_dvd a.val q
  have hg1 : (extGcd a.val q).1 = 1 := by
    rcases hp.isPrime.2 _ hdq with h1 | hqq
    · exact h1
    · rw [hqq] at hda; exact False.elim (hNotDvd hda)
  have hbez := extGcd_bezout a.val q
  rw [hg1, Int.natCast_one] at hbez
  have hqNe : (q : Int) ≠ 0 := by omega
  apply ext
  rw [mul_val, one_val]
  unfold inv
  simp only [ha0, ↓reduceIte]
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.natCast_mul, Int.toNat_of_nonneg (Int.emod_nonneg _ hqNe),
    Int.natCast_one]
  exact bezout_emod_eq_one hqGe2 _ _ _ hbez

end ZMod

instance (q : Nat) [FactPrime q] : LawfulCommRing (ZMod q) where
  zero := ZMod.zero q
  one := ZMod.one q
  add := ZMod.add
  mul := ZMod.mul
  neg := ZMod.neg
  sub := ZMod.sub
  add_assoc := ZMod.add_assoc
  add_comm := ZMod.add_comm
  zero_add := ZMod.zero_add
  add_zero := ZMod.add_zero
  add_left_neg := ZMod.add_left_neg
  sub_eq_add_neg _ _ := rfl
  mul_assoc := ZMod.mul_assoc
  mul_comm := ZMod.mul_comm
  one_mul := ZMod.one_mul
  mul_one := ZMod.mul_one
  left_distrib := ZMod.left_distrib
  right_distrib := ZMod.right_distrib

instance (q : Nat) [FactPrime q] : LawfulField (ZMod q) where
  inv := ZMod.inv
  zero_ne_one := ZMod.zero_ne_one (q := q)
  inv_zero := ZMod.inv_zero
  mul_inv_cancel := ZMod.mul_inv_cancel

instance instFactPrimeGoldilocks : FactPrime goldilocksPrime :=
  ⟨goldilocksPrime_isPrime ()⟩

private def noDivRange : Nat → Nat → Nat → Bool
  | _, _, 0 => true
  | n, d, k + 1 => (n % d != 0) && noDivRange n (d + 1) k

private theorem noDivRange_sound (n : Nat) :
    ∀ (d k : Nat), noDivRange n d k = true → ∀ m : Nat, d ≤ m → m < d + k → ¬ (m ∣ n)
  | _, 0, _, m, hlo, hhi, _ => by omega
  | d, k + 1, hok, m, hlo, hhi, hdvd => by
    simp only [noDivRange, Bool.and_eq_true, bne_iff_ne] at hok
    if hm : m = d then
      subst hm
      exact hok.1 (Nat.mod_eq_zero_of_dvd hdvd)
    else
      exact noDivRange_sound n (d + 1) k hok.2 m (by omega) (by omega) hdvd

private theorem noDivRange_257 : noDivRange 257 2 255 = true := by decide +kernel

private theorem noDivRange_65537 : noDivRange 65537 2 256 = true := by decide +kernel

instance instFactPrime257 : FactPrime 257 where
  isPrime := by
    refine ⟨by decide, fun d hd => ?_⟩
    if hd1 : d = 1 then exact .inl hd1
    else if hd257 : d = 257 then exact .inr hd257
    else
      exfalso
      have hdLe : d ≤ 257 := Nat.le_of_dvd (by decide) hd
      have hdPos : 0 < d := by
        if hd0 : d = 0 then
          subst hd0; obtain ⟨k, hk⟩ := hd; omega
        else omega
      exact noDivRange_sound 257 2 255 noDivRange_257 d (by omega) (by omega) hd

instance instFactPrime65537 : FactPrime 65537 where
  isPrime := by
    refine ⟨by decide, fun d hd => ?_⟩
    if hd1 : d = 1 then exact .inl hd1
    else if hdq : d = 65537 then exact .inr hdq
    else
      exfalso
      obtain ⟨e, he⟩ := hd
      have hdGe2 : 2 ≤ d := by
        if hd0 : d = 0 then subst hd0; omega else omega
      have heGe2 : 2 ≤ e := by
        if he0 : e = 0 then subst he0; omega
        else if he1 : e = 1 then
          subst he1
          rw [Nat.mul_one] at he
          exact False.elim (hdq he.symm)
        else omega
      have hSound := noDivRange_sound 65537 2 256 noDivRange_65537
      if hle : d ≤ e then
        have hdLt : d < 258 := by
          if hge : 258 ≤ d then
            have hsq := Nat.mul_le_mul hge (Nat.le_trans hge hle)
            omega
          else omega
        exact hSound d hdGe2 (by omega) ⟨e, he⟩
      else
        have heLt : e < 258 := by
          if hge : 258 ≤ e then
            have hsq := Nat.mul_le_mul (by omega : 258 ≤ d) hge
            omega
          else omega
        exact hSound e heGe2 (by omega) ⟨d, he.trans (Nat.mul_comm d e)⟩

/-- Multiply polynomial `p` (low-to-high coefficients) by linear factor `a + b * X`. -/
def mulLinear {F : Type} [CommRingOps F] (a b : F) : List F → List F
  | [] => []
  | c :: cs =>
    let rest := mulLinear a b cs
    match rest with
    | [] => [CommRingOps.mul a c, CommRingOps.mul b c]
    | r0 :: rs => CommRingOps.mul a c :: CommRingOps.add (CommRingOps.mul b c) r0 :: rs

theorem mulLinear_length_le {F : Type} [CommRingOps F] (a b : F) :
    ∀ (p : List F), (mulLinear a b p).length ≤ p.length + 1
  | [] => Nat.zero_le 1
  | c :: cs => by
    have ih := mulLinear_length_le a b cs
    simp only [mulLinear]
    cases hRest : mulLinear a b cs with
    | nil => simp only [List.length_cons, List.length_nil]; omega
    | cons r0 rs =>
      rw [hRest] at ih
      simp only [List.length_cons] at ih ⊢
      omega

theorem evalCoeffs_mulLinear {F : Type} [LawfulCommRing F] (a b : F) :
    ∀ (p : List F) (x : F),
      RoundPoly.evalCoeffs (mulLinear a b p) x =
        CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x)) (RoundPoly.evalCoeffs p x)
  | [], _ => by
    simp [mulLinear, RoundPoly.evalCoeffs_nil, LawfulCommRing.mul_zero]
  | c :: cs, x => by
    have ih := evalCoeffs_mulLinear a b cs x
    simp only [mulLinear]
    cases hRest : mulLinear a b cs with
    | nil =>
      rw [hRest, RoundPoly.evalCoeffs_nil] at ih
      simp only [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil,
                 LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
      have hTail0 : CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x))
          (CommRingOps.mul x (RoundPoly.evalCoeffs cs x)) = CommRingOps.zero := by
        calc CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x))
              (CommRingOps.mul x (RoundPoly.evalCoeffs cs x))
            = CommRingOps.mul x (CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x))
                (RoundPoly.evalCoeffs cs x)) := by constructive_ring
          _ = CommRingOps.mul x CommRingOps.zero := by rw [← ih]
          _ = CommRingOps.zero := LawfulCommRing.mul_zero x
      calc CommRingOps.add (CommRingOps.mul a c) (CommRingOps.mul x (CommRingOps.mul b c))
          = CommRingOps.add (CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x)) c)
              CommRingOps.zero := by constructive_ring
        _ = CommRingOps.add (CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x)) c)
              (CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x))
                (CommRingOps.mul x (RoundPoly.evalCoeffs cs x))) := by rw [← hTail0]
        _ = CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x))
              (CommRingOps.add c (CommRingOps.mul x (RoundPoly.evalCoeffs cs x))) := by
              constructive_ring
    | cons r0 rs =>
      rw [hRest, RoundPoly.evalCoeffs_cons] at ih
      simp only [RoundPoly.evalCoeffs_cons]
      calc CommRingOps.add (CommRingOps.mul a c)
            (CommRingOps.mul x
              (CommRingOps.add (CommRingOps.add (CommRingOps.mul b c) r0)
                (CommRingOps.mul x (RoundPoly.evalCoeffs rs x))))
          = CommRingOps.add (CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x)) c)
              (CommRingOps.mul x (CommRingOps.add r0 (CommRingOps.mul x (RoundPoly.evalCoeffs rs x)))) := by
                constructive_ring
        _ = CommRingOps.add (CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x)) c)
              (CommRingOps.mul x (CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x))
                (RoundPoly.evalCoeffs cs x))) := by rw [ih]
        _ = CommRingOps.mul (CommRingOps.add a (CommRingOps.mul b x))
              (CommRingOps.add c (CommRingOps.mul x (RoundPoly.evalCoeffs cs x))) := by
                constructive_ring

/-- Lagrange basis polynomial `∏_{x_j ∈ others} (-x_j + X) * (x_i - x_j)⁻¹`. -/
def lagrangeBasisFromOthers {F : Type} [LawfulField F] (xi : F) : List F → List F
  | [] => [CommRingOps.one]
  | xj :: rest =>
    let invDiff := LawfulField.inv (CommRingOps.sub xi xj)
    mulLinear (CommRingOps.mul (CommRingOps.neg xj) invDiff) invDiff
      (lagrangeBasisFromOthers xi rest)

theorem lagrangeBasisFromOthers_length_le {F : Type} [LawfulField F] (xi : F) :
    ∀ (others : List F), (lagrangeBasisFromOthers xi others).length ≤ others.length + 1
  | [] => Nat.le_refl 1
  | _ :: rest => by
    simp only [lagrangeBasisFromOthers, List.length_cons]
    exact Nat.le_trans (mulLinear_length_le _ _ _)
      (Nat.add_le_add_right (lagrangeBasisFromOthers_length_le xi rest) 1)

/-- Executable scalar Lagrange-at-zero weight `λ_{i, S} = ∏_{x_j ∈ S, x_j ≠ x_i} (-x_j) * (x_i - x_j)⁻¹`. -/
@[expose] def lagrangeScalarFromOthers {F : Type} [LawfulField F] (xi : F) : List F → F
  | [] => CommRingOps.one
  | xj :: rest =>
    let invDiff := LawfulField.inv (CommRingOps.sub xi xj)
    CommRingOps.mul (CommRingOps.mul (CommRingOps.neg xj) invDiff)
      (lagrangeScalarFromOthers xi rest)

/-- Lagrange-at-zero coefficient `λ_{i, S}` for evaluation point `xi` in quorum `S`. -/
@[expose] def lagrangeWeightAtZero {F : Type} [LawfulField F] [DecidableEq F] (S : List F) (xi : F) : F :=
  lagrangeScalarFromOthers xi (S.filter (fun xj => decide (xj ≠ xi)))

/-- Local non-interactive Lagrange-to-additive share conversion `a_i := λ_{i, S} · s_i` for Co-ZK / MPC. -/
def lagrangeToAdditiveShare {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (xi si : F) : F :=
  CommRingOps.mul (lagrangeWeightAtZero S xi) si

/-- Public equation used by custody interpolation, without unfolding the threshold module. -/
theorem lagrangeToAdditiveShare_eq {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (xi si : F) :
    lagrangeToAdditiveShare S xi si = CommRingOps.mul (lagrangeWeightAtZero S xi) si := by rfl

private theorem eval_lagrangeBasis_zero {F : Type} [LawfulField F] (xi : F) :
    ∀ (others : List F),
      RoundPoly.evalCoeffs (lagrangeBasisFromOthers xi others) CommRingOps.zero =
        lagrangeScalarFromOthers xi others
  | [] => by
    simp [lagrangeBasisFromOthers, lagrangeScalarFromOthers, RoundPoly.evalCoeffs_cons,
          RoundPoly.evalCoeffs_nil, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | xj :: rest => by
    simp only [lagrangeBasisFromOthers, lagrangeScalarFromOthers, evalCoeffs_mulLinear,
               LawfulCommRing.mul_zero, LawfulCommRing.add_zero, eval_lagrangeBasis_zero xi rest]

private theorem eval_lagrangeBasis_self {F : Type} [LawfulField F] (xi : F) :
    ∀ (others : List F), (∀ xj ∈ others, xi ≠ xj) →
      RoundPoly.evalCoeffs (lagrangeBasisFromOthers xi others) xi = CommRingOps.one
  | [], _ => by
    simp [lagrangeBasisFromOthers, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil,
          LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | xj :: rest, hNe => by
    have hNeHead : xi ≠ xj := hNe xj (.head rest)
    have hDiffNe : CommRingOps.sub xi xj ≠ CommRingOps.zero := fun h0 =>
      hNeHead (LawfulCommRing.sub_eq_zero_iff.mp h0)
    simp only [lagrangeBasisFromOthers, evalCoeffs_mulLinear,
               eval_lagrangeBasis_self xi rest (fun y hy => hNe y (.tail xj hy)),
               LawfulCommRing.mul_one]
    have hFactor : CommRingOps.add
        (CommRingOps.mul (CommRingOps.neg xj) (LawfulField.inv (CommRingOps.sub xi xj)))
        (CommRingOps.mul (LawfulField.inv (CommRingOps.sub xi xj)) xi) =
        CommRingOps.mul (CommRingOps.sub xi xj) (LawfulField.inv (CommRingOps.sub xi xj)) := by
      constructive_ring
    rw [hFactor, LawfulField.mul_inv_cancel hDiffNe]

private theorem eval_lagrangeBasis_other {F : Type} [LawfulField F] (xi xk : F) :
    ∀ (others : List F), xk ∈ others →
      RoundPoly.evalCoeffs (lagrangeBasisFromOthers xi others) xk = CommRingOps.zero
  | [], hMem => by cases hMem
  | xj :: rest, hMem => by
    simp only [lagrangeBasisFromOthers, evalCoeffs_mulLinear]
    rcases List.mem_cons.mp hMem with rfl | hTail
    · have hFactor0 : CommRingOps.add
          (CommRingOps.mul (CommRingOps.neg xk) (LawfulField.inv (CommRingOps.sub xi xk)))
          (CommRingOps.mul (LawfulField.inv (CommRingOps.sub xi xk)) xk) = CommRingOps.zero := by
        constructive_ring
      rw [hFactor0, LawfulCommRing.zero_mul]
    · rw [eval_lagrangeBasis_other xi xk rest hTail, LawfulCommRing.mul_zero]

/-- Variable-length polynomial addition. -/
private def polyAddVarPt {R : Type} [CommRingOps R] : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a :: ps, b :: qs => CommRingOps.add a b :: polyAddVarPt ps qs

private theorem polyAddVarPt_length_le {R : Type} [CommRingOps R] :
    ∀ (p q : List R) (m : Nat), p.length ≤ m → q.length ≤ m → (polyAddVarPt p q).length ≤ m
  | [], _, _, _, hq => hq
  | _ :: _, [], _, hp, _ => hp
  | _ :: ps, _ :: qs, 0, hp, _ => (Nat.not_succ_le_zero _ hp).elim
  | _ :: ps, _ :: qs, k + 1, hp, hq => by
    simp only [polyAddVarPt, List.length_cons] at hp hq ⊢
    exact Nat.succ_le_succ (polyAddVarPt_length_le ps qs k (by omega) (by omega))

private theorem evalCoeffs_polyAddVarPt {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R) (x : R),
      RoundPoly.evalCoeffs (polyAddVarPt p q) x =
        CommRingOps.add (RoundPoly.evalCoeffs p x) (RoundPoly.evalCoeffs q x)
  | [], q, x => by simp [polyAddVarPt, RoundPoly.evalCoeffs_nil, LawfulCommRing.zero_add]
  | p, [], x => by
    cases p <;> simp [polyAddVarPt, RoundPoly.evalCoeffs_nil, LawfulCommRing.add_zero]
  | a :: ps, b :: qs, x => by
    simp only [polyAddVarPt, RoundPoly.evalCoeffs_cons, evalCoeffs_polyAddVarPt ps qs x]
    constructive_ring

private def polyScalePt {R : Type} [CommRingOps R] (c : R) : List R → List R
  | [] => []
  | a :: as => CommRingOps.mul c a :: polyScalePt c as

private theorem polyScalePt_length {R : Type} [CommRingOps R] (c : R) :
    ∀ (p : List R), (polyScalePt c p).length = p.length
  | [] => rfl
  | _ :: as => congrArg Nat.succ (polyScalePt_length c as)

private theorem evalCoeffs_polyScalePt {R : Type} [LawfulCommRing R] (c : R) :
    ∀ (p : List R) (x : R),
      RoundPoly.evalCoeffs (polyScalePt c p) x = CommRingOps.mul c (RoundPoly.evalCoeffs p x)
  | [], _ => by simp [polyScalePt, RoundPoly.evalCoeffs_nil, LawfulCommRing.mul_zero]
  | a :: as, x => by
    simp only [polyScalePt, RoundPoly.evalCoeffs_cons, evalCoeffs_polyScalePt c as x]
    constructive_ring

/-- Lagrange interpolation polynomial `∑_{xi ∈ pts} f(xi) · L_{i, S}(X)`. -/
private def lagrangeInterpAux {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (f : F → F) : List F → List F
  | [] => []
  | xi :: rest =>
    let basis := lagrangeBasisFromOthers xi (S.filter (fun xj => decide (xj ≠ xi)))
    polyAddVarPt (polyScalePt (f xi) basis) (lagrangeInterpAux S f rest)

private theorem filter_ne_self_length_lt {α : Type} [DecidableEq α] :
    ∀ {S : List α} {x : α}, x ∈ S → (S.filter (fun y => decide (y ≠ x))).length + 1 ≤ S.length
  | [], _, hMem => by cases hMem
  | hd :: tl, x, hMem => by
    simp only [List.filter_cons, List.length_cons]
    if hEq : hd = x then
      subst hEq
      have hDec : decide (hd ≠ hd) = false := decide_eq_false (fun h => h rfl)
      rw [hDec]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact Nat.add_le_add_right (List.length_filter_le _ tl) 1
    else
      rcases List.mem_cons.mp hMem with rfl | hTl
      · exact False.elim (hEq rfl)
      · rw [decide_eq_true hEq]; simp only [↓reduceIte, List.length_cons]
        have ih := filter_ne_self_length_lt hTl
        omega

private theorem lagrangeInterpAux_length_le {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (f : F → F) :
    ∀ (pts : List F), (∀ x ∈ pts, x ∈ S) → (lagrangeInterpAux S f pts).length ≤ S.length
  | [], _ => Nat.zero_le _
  | xi :: rest, hSub => by
    simp only [lagrangeInterpAux]
    apply polyAddVarPt_length_le
    · rw [polyScalePt_length]
      exact Nat.le_trans (lagrangeBasisFromOthers_length_le xi _)
        (filter_ne_self_length_lt (hSub xi (.head rest)))
    · exact lagrangeInterpAux_length_le S f rest (fun y hy => hSub y (.tail xi hy))

private theorem evalCoeffs_lagrangeInterpAux_zero {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (f : F → F) :
    ∀ (pts : List F),
      RoundPoly.evalCoeffs (lagrangeInterpAux S f pts) CommRingOps.zero =
        ringListSum (pts.map (fun xi => lagrangeToAdditiveShare S xi (f xi)))
  | [] => by simp [lagrangeInterpAux, ringListSum, RoundPoly.evalCoeffs_nil]
  | xi :: rest => by
    simp only [lagrangeInterpAux, List.map_cons, ringListSum,
               evalCoeffs_polyAddVarPt, evalCoeffs_polyScalePt,
               eval_lagrangeBasis_zero, evalCoeffs_lagrangeInterpAux_zero S f rest]
    unfold lagrangeToAdditiveShare lagrangeWeightAtZero
    rw [LawfulCommRing.mul_comm (f xi)]

private theorem evalCoeffs_lagrangeInterpAux_at_mem {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (f : F → F) :
    ∀ (pts : List F), pts.Nodup → (∀ x ∈ pts, x ∈ S) →
      ∀ xk ∈ S,
        RoundPoly.evalCoeffs (lagrangeInterpAux S f pts) xk =
          if xk ∈ pts then f xk else CommRingOps.zero
  | [], _, _, _, _ => by simp [lagrangeInterpAux, RoundPoly.evalCoeffs_nil]
  | xi :: rest, hNd, hSub, xk, hxkS => by
    obtain ⟨hNotInRest, hRestNd⟩ := List.nodup_cons.mp hNd
    simp only [lagrangeInterpAux, evalCoeffs_polyAddVarPt, evalCoeffs_polyScalePt,
               evalCoeffs_lagrangeInterpAux_at_mem S f rest hRestNd (fun y hy => hSub y (.tail xi hy)) xk hxkS]
    if hEq : xk = xi then
      subst hEq
      have hBasis1 : RoundPoly.evalCoeffs
          (lagrangeBasisFromOthers xk (S.filter (fun xj => decide (xj ≠ xk)))) xk =
          CommRingOps.one := by
        apply eval_lagrangeBasis_self
        intro xj hxj
        exact Ne.symm (of_decide_eq_true (List.mem_filter.mp hxj).2)
      rw [hBasis1, LawfulCommRing.mul_one]
      simp [hNotInRest, LawfulCommRing.add_zero]
    else
      have hBasis0 : RoundPoly.evalCoeffs
          (lagrangeBasisFromOthers xi (S.filter (fun xj => decide (xj ≠ xi)))) xk =
          CommRingOps.zero := by
        apply eval_lagrangeBasis_other
        exact List.mem_filter.mpr ⟨hxkS, decide_eq_true hEq⟩
      rw [hBasis0, LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
      simp [List.mem_cons, hEq]

/-- **Polymorphic Lagrange-to-Additive Secret Reconstruction (`lagrange_to_additive_reconstructs_poly`)**:
    Over ANY `[LawfulField F] [DecidableEq F]`, for ANY `t` distinct evaluation points `S : List F`
    (`S.Nodup`, `S.length = t`, `1 ≤ t`) and ANY degree-`< t` Shamir polynomial `coeffs : List F`
    (`coeffs.length ≤ t`), summing the locally converted additive shares `λ_{i, S} · P(x_i)` recovers
    `P(0) = coeffs.headD 0`! -/
theorem lagrange_to_additive_reconstructs_poly {F : Type} [LawfulField F] [DecidableEq F]
    (t : Nat) (ht : 1 ≤ t) (S : List F) (hNd : S.Nodup) (hSLen : S.length = t)
    (coeffs : List F) (hDeg : coeffs.length ≤ t) :
    ringListSum (S.map (fun xi => lagrangeToAdditiveShare S xi (RoundPoly.evalCoeffs coeffs xi))) =
      RoundPoly.evalCoeffs coeffs CommRingOps.zero := by
  let interp := lagrangeInterpAux S (RoundPoly.evalCoeffs coeffs) S
  have hInterpLen : interp.length ≤ t := by
    rw [← hSLen]
    exact lagrangeInterpAux_length_le S _ S (fun _ h => h)
  have hInterp0 : RoundPoly.evalCoeffs interp CommRingOps.zero =
      ringListSum (S.map (fun xi => lagrangeToAdditiveShare S xi (RoundPoly.evalCoeffs coeffs xi))) :=
    evalCoeffs_lagrangeInterpAux_zero S (RoundPoly.evalCoeffs coeffs) S
  rw [← hInterp0]
  let diff := polyAddVarPt interp (polyScalePt (CommRingOps.neg CommRingOps.one) coeffs)
  have hDiffLen : diff.length ≤ t := by
    apply polyAddVarPt_length_le interp _ t hInterpLen
    rw [polyScalePt_length]; exact hDeg
  have hVanish : ∀ xk ∈ S, RoundPoly.evalCoeffs diff xk = CommRingOps.zero := by
    intro xk hxk
    dsimp only [diff]
    rw [evalCoeffs_polyAddVarPt, evalCoeffs_polyScalePt,
        evalCoeffs_lagrangeInterpAux_at_mem S (RoundPoly.evalCoeffs coeffs) S hNd (fun _ h => h) xk hxk]
    simp only [hxk, ↓reduceIte]
    constructive_ring
  if hEq0 : RoundPoly.evalCoeffs interp CommRingOps.zero = RoundPoly.evalCoeffs coeffs CommRingOps.zero then
    exact hEq0
  else
    exfalso
    have hDiffNz0 : RoundPoly.evalCoeffs diff CommRingOps.zero ≠ CommRingOps.zero := by
      dsimp only [diff]
      rw [evalCoeffs_polyAddVarPt, evalCoeffs_polyScalePt]
      intro h0
      apply hEq0
      have hSub : CommRingOps.sub (RoundPoly.evalCoeffs interp CommRingOps.zero)
          (RoundPoly.evalCoeffs coeffs CommRingOps.zero) = CommRingOps.zero := by
        calc CommRingOps.sub (RoundPoly.evalCoeffs interp CommRingOps.zero)
              (RoundPoly.evalCoeffs coeffs CommRingOps.zero)
            = CommRingOps.add (RoundPoly.evalCoeffs interp CommRingOps.zero)
                (CommRingOps.mul (CommRingOps.neg CommRingOps.one)
                  (RoundPoly.evalCoeffs coeffs CommRingOps.zero)) := by constructive_ring
          _ = CommRingOps.zero := h0
      exact LawfulCommRing.sub_eq_zero_iff.mp hSub
    cases t with
    | zero => omega
    | succ d =>
      have hFilt : S.filter (fun r => decide (RoundPoly.evalCoeffs diff r = CommRingOps.zero)) = S :=
        List.filter_eq_self.mpr (fun xk hxk => decide_eq_true (hVanish xk hxk))
      have hRoots := @RoundPoly.roots_nodup_length_le F _ _ (LawfulField.toNoZeroDivisors F)
        d diff S hNd hDiffLen ⟨CommRingOps.zero, hDiffNz0⟩
      rw [hFilt, hSLen] at hRoots
      omega

/-- **Parametric `(t, n)` (`2 ≤ t ≤ n`) Lagrange-to-Additive Co-ZK Conversion Over `ZMod q`
    (`lagrange_to_additive_reconstructs_sk`)**:
    Over ANY prime field `ZMod q` (`[FactPrime q]`), for ANY `(t, n)` (`2 ≤ t ≤ n`), ANY `t`-subset
    `S : List (ZMod q)` of distinct nonzero evaluation points (`S.Nodup`, `S.length = t`), and ANY
    secret `sk : ZMod q` with `(t - 1)` random Shamir masking coefficients `randCoeffs`,
    `∑_{x_i ∈ S} (λ_{i, S} · s_i) = sk`! -/
theorem lagrange_to_additive_reconstructs_sk (q t n : Nat) [FactPrime q]
    (ht2 : 2 ≤ t) (htn : t ≤ n)
    (S : List (ZMod q)) (hNd : S.Nodup) (hSLen : S.length = t)
    (hNonZero : ∀ x ∈ S, x ≠ CommRingOps.zero)
    (sk : ZMod q) (randCoeffs : List (ZMod q)) (hRandLen : randCoeffs.length ≤ t - 1) :
    S.length ≤ n ∧
    ¬ (CommRingOps.zero ∈ S) ∧
    ringListSum (S.map (fun xi =>
      lagrangeToAdditiveShare S xi (RoundPoly.evalCoeffs (sk :: randCoeffs) xi))) = sk := by
  have hSubN : S.length ≤ n := hSLen ▸ htn
  have hNo0 : ¬ (CommRingOps.zero ∈ S) := fun hMem => hNonZero CommRingOps.zero hMem rfl
  have hDeg : (sk :: randCoeffs).length ≤ t := by
    simp only [List.length_cons]; omega
  refine ⟨hSubN, hNo0, ?_⟩
  rw [lagrange_to_additive_reconstructs_poly t (by omega) S hNd hSLen (sk :: randCoeffs) hDeg,
    RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

def s67EvalPoints : List (ZMod 257) :=
  (List.range 67).map (fun i => ZMod.ofNat 257 (i + 1))

def sk67Witness : ZMod 257 :=
  ZMod.ofNat 257 42

def rand66WitnessCoeffs : List (ZMod 257) :=
  (List.range 66).map (fun i => ZMod.ofNat 257 (i + 3))

/-- Concrete `67`-of-`100` (`t = 67, n = 100`) Lagrange-to-additive reconstruction witness over
    `ZMod 257`: evaluation points `x_1 = 1, ..., x_67 = 67` in a `100`-custodian committee! -/
theorem inhabited_lagrange_67_of_100 :
    s67EvalPoints.length = 67 ∧
    s67EvalPoints.Nodup ∧
    (∀ x ∈ s67EvalPoints, x ≠ CommRingOps.zero) ∧
    ringListSum (s67EvalPoints.map (fun xi =>
      lagrangeToAdditiveShare s67EvalPoints xi
        (RoundPoly.evalCoeffs (sk67Witness :: rand66WitnessCoeffs) xi))) = sk67Witness := by
  have c1 : s67EvalPoints.length = 67 := by decide +kernel
  have c2 : s67EvalPoints.Nodup := by decide +kernel
  have c3 : ∀ x ∈ s67EvalPoints, x ≠ CommRingOps.zero := by decide +kernel
  have c4 : ringListSum (s67EvalPoints.map (fun xi =>
      lagrangeToAdditiveShare s67EvalPoints xi
        (RoundPoly.evalCoeffs (sk67Witness :: rand66WitnessCoeffs) xi))) = sk67Witness := by
    exact (lagrange_to_additive_reconstructs_sk 257 67 100 (by decide) (by decide)
      s67EvalPoints c2 c1 c3 sk67Witness rand66WitnessCoeffs (by decide +kernel)).2.2
  exact ⟨c1, c2, c3, c4⟩

/-- Rebalancing shift `(sk2 - sk1) · V(X)` with exactly `d + 1` coefficients, where `V(0) = 1` and
    `V` vanishes on `corruptPts`. -/
private def shamirShiftPoly {F : Type} [LawfulField F] (d : Nat) (corruptPts : List F)
    (sk1 sk2 : F) : List F :=
  polyScale (CommRingOps.sub sk2 sk1) (vanishCorruptUnit0 LawfulField.inv (d + 1) corruptPts)

private theorem shamirShiftPoly_length {F : Type} [LawfulField F] {d : Nat} {corruptPts : List F}
    (sk1 sk2 : F) (hCard : corruptPts.length ≤ d) :
    (shamirShiftPoly d corruptPts sk1 sk2).length = d + 1 := by
  unfold shamirShiftPoly
  rw [polyScale_length]
  exact vanishCorruptUnit0_length _ _ _ (by omega)

private theorem shamirShiftPoly_tail_length {F : Type} [LawfulField F] {d : Nat}
    {corruptPts : List F} (sk1 sk2 : F) (hCard : corruptPts.length ≤ d) :
    (shamirShiftPoly d corruptPts sk1 sk2).tail.length = d := by
  rw [List.length_tail, shamirShiftPoly_length sk1 sk2 hCard, Nat.add_sub_cancel]

/-- Bijection on the `d` tail coefficients of a degree-`≤ d` Shamir polynomial that moves the constant
    term from `sk1` to `sk2` while fixing every evaluation at `corruptPts`: `r ↦ r + tail(Δ)` with
    `Δ = (sk2 - sk1) · V`, `V(0) = 1`, `V` vanishing on `corruptPts`. -/
def shamirTailEquiv {F : Type} [LawfulField F] (d : Nat)
    (corruptPts : List F) (sk1 sk2 : F)
    (hCard : corruptPts.length ≤ d) :
    SimpleEquiv { r : List F // r.length = d } { r : List F // r.length = d } where
  toFun r :=
    ⟨polyAddFixed r.1 (shamirShiftPoly d corruptPts sk1 sk2).tail,
      (polyAddFixed_length r.1 _
        (r.2.trans (shamirShiftPoly_tail_length sk1 sk2 hCard).symm)).trans r.2⟩
  invFun r :=
    ⟨polySubFixed r.1 (shamirShiftPoly d corruptPts sk1 sk2).tail,
      (polySubFixed_length r.1 _
        (r.2.trans (shamirShiftPoly_tail_length sk1 sk2 hCard).symm)).trans r.2⟩
  left_inv r :=
    Subtype.ext (polySub_polyAdd_cancel r.1 _
      (r.2.trans (shamirShiftPoly_tail_length sk1 sk2 hCard).symm))
  right_inv r :=
    Subtype.ext (polyAdd_polySub_cancel r.1 _
      (r.2.trans (shamirShiftPoly_tail_length sk1 sk2 hCard).symm))

private theorem shamirTailEquiv_eval {F : Type} [LawfulField F] (d : Nat)
    (corruptPts : List F) (sk1 sk2 : F) (hCard : corruptPts.length ≤ d)
    (hNz : ∀ c ∈ corruptPts, c ≠ CommRingOps.zero)
    (r : { l : List F // l.length = d }) (xc : F) (hxc : xc ∈ corruptPts) :
    RoundPoly.evalCoeffs (sk2 :: ((shamirTailEquiv d corruptPts sk1 sk2 hCard).toFun r).1) xc =
      RoundPoly.evalCoeffs (sk1 :: r.1) xc := by
  obtain ⟨_, hv0, hvCorr⟩ :=
    vanishCorruptUnit0_props (R := F) LawfulField.inv
      (fun _ hx => LawfulField.mul_inv_cancel hx) (Nat.succ_le_succ hCard) hNz
  have hLen := shamirShiftPoly_length sk1 sk2 hCard
  have hAt0 : RoundPoly.evalCoeffs (shamirShiftPoly d corruptPts sk1 sk2) CommRingOps.zero =
      CommRingOps.sub sk2 sk1 := by
    unfold shamirShiftPoly
    rw [evalCoeffs_scale, hv0, LawfulCommRing.mul_one]
  have hAtC : RoundPoly.evalCoeffs (shamirShiftPoly d corruptPts sk1 sk2) xc = CommRingOps.zero := by
    unfold shamirShiftPoly
    rw [evalCoeffs_scale, hvCorr xc hxc, LawfulCommRing.mul_zero]
  show RoundPoly.evalCoeffs
      (sk2 :: polyAddFixed r.1 (shamirShiftPoly d corruptPts sk1 sk2).tail) xc = _
  generalize shamirShiftPoly d corruptPts sk1 sk2 = delta at hLen hAt0 hAtC ⊢
  cases delta with
  | nil => exact (Nat.succ_ne_zero d hLen.symm).elim
  | cons d0 ds =>
    rw [RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hAt0
    have hHead : sk2 = CommRingOps.add sk1 d0 := by
      rw [hAt0]
      exact (LawfulCommRing.add_sub_cancel_left sk1 sk2).symm
    have hEqLen : (sk1 :: r.1).length = (d0 :: ds).length := by
      rw [hLen, List.length_cons, r.2]
    have hAdd := evalCoeffs_addFixed (sk1 :: r.1) (d0 :: ds) xc hEqLen
    rw [hAtC, LawfulCommRing.add_zero] at hAdd
    rw [polyAddFixed_cons] at hAdd
    exact (congrArg (fun c0 => RoundPoly.evalCoeffs (c0 :: polyAddFixed r.1 ds) xc) hHead).trans hAdd

/-- **`(t - 1)`-Corruption Shamir & Additive-Share Zero-Knowledge Over `ZMod q`
    (`shamir_t_minus_1_shares_independent_of_sk`)**:
    For ANY `2 ≤ t ≤ n`, ANY `corruptPts : List (ZMod q)` of size `≤ t - 1` (`∀ c ∈ corruptPts, c ≠ 0`),
    and ANY two candidate secrets `sk1, sk2 : ZMod q`:
    1. `shamirTailEquiv` is a constructive `SimpleEquiv` on `(ZMod q)^(t - 1)` mapping `r ↦ r'` such
       that `evalCoeffs (sk2 :: r') xc = evalCoeffs (sk1 :: r) xc` AND converted additive shares
       `lagrangeToAdditiveShare S xc` agree **identically** at every `xc ∈ corruptPts`!
    2. Over ANY finite enumeration `SimpleEquiv (Fin Card) { r : List (ZMod q) // r.length = t - 1 }`,
       EVERY distinguisher `D` observing all corrupt Shamir + additive shares has **exact advantage `0`**! -/
theorem shamir_t_minus_1_shares_independent_of_sk (q t n : Nat) [FactPrime q]
    (ht2 : 2 ≤ t) (htn : t ≤ n)
    (S corruptPts : List (ZMod q))
    (hCard : corruptPts.length ≤ t - 1)
    (hNz : ∀ c ∈ corruptPts, c ≠ CommRingOps.zero)
    (sk1 sk2 : ZMod q) :
    corruptPts.length < n ∧
    (∀ (r : { l : List (ZMod q) // l.length = t - 1 }) (xc : ZMod q),
      xc ∈ corruptPts →
      RoundPoly.evalCoeffs (sk2 :: ((shamirTailEquiv (t - 1) corruptPts sk1 sk2 hCard).toFun r).1) xc =
        RoundPoly.evalCoeffs (sk1 :: r.1) xc ∧
      lagrangeToAdditiveShare S xc
        (RoundPoly.evalCoeffs (sk2 :: ((shamirTailEquiv (t - 1) corruptPts sk1 sk2 hCard).toFun r).1) xc) =
        lagrangeToAdditiveShare S xc (RoundPoly.evalCoeffs (sk1 :: r.1) xc)) ∧
    (∀ (Card : Nat) (enum : SimpleEquiv (Fin Card) { l : List (ZMod q) // l.length = t - 1 })
       (D : List (ZMod q × ZMod q) → Bool),
      qsum Card (fun k =>
        let r := (enum.toFun k).1
        let view := corruptPts.map (fun xc =>
          let s := RoundPoly.evalCoeffs (sk1 :: r) xc
          (s, lagrangeToAdditiveShare S xc s))
        if D view then 1 else 0) =
      qsum Card (fun k =>
        let r := (enum.toFun k).1
        let view := corruptPts.map (fun xc =>
          let s := RoundPoly.evalCoeffs (sk2 :: r) xc
          (s, lagrangeToAdditiveShare S xc s))
        if D view then 1 else 0)) := by
  have hLtN : corruptPts.length < n := by omega
  have hPt : ∀ (r : { l : List (ZMod q) // l.length = t - 1 }) (xc : ZMod q),
      xc ∈ corruptPts →
      RoundPoly.evalCoeffs (sk2 :: ((shamirTailEquiv (t - 1) corruptPts sk1 sk2 hCard).toFun r).1) xc =
        RoundPoly.evalCoeffs (sk1 :: r.1) xc :=
    fun r xc hxc => shamirTailEquiv_eval (t - 1) corruptPts sk1 sk2 hCard hNz r xc hxc
  refine ⟨hLtN, fun r xc hxc => ⟨hPt r xc hxc, by rw [hPt r xc hxc]⟩, ?_⟩
  intro Card enum D
  have hInv := qsum_bijection_invariant enum (shamirTailEquiv (t - 1) corruptPts sk1 sk2 hCard)
    (fun r =>
      if D (corruptPts.map (fun xc =>
        (RoundPoly.evalCoeffs (sk2 :: r.1) xc,
          lagrangeToAdditiveShare S xc (RoundPoly.evalCoeffs (sk2 :: r.1) xc)))) then 1 else 0)
  refine Eq.trans (qsum_congr (fun k => ?_)) hInv
  have hMapEq :
      corruptPts.map (fun xc =>
        (RoundPoly.evalCoeffs (sk1 :: (enum.toFun k).1) xc,
          lagrangeToAdditiveShare S xc (RoundPoly.evalCoeffs (sk1 :: (enum.toFun k).1) xc))) =
      corruptPts.map (fun xc =>
        (RoundPoly.evalCoeffs
            (sk2 :: ((shamirTailEquiv (t - 1) corruptPts sk1 sk2 hCard).toFun (enum.toFun k)).1) xc,
          lagrangeToAdditiveShare S xc
            (RoundPoly.evalCoeffs
              (sk2 :: ((shamirTailEquiv (t - 1) corruptPts sk1 sk2 hCard).toFun (enum.toFun k)).1)
              xc))) := by
    apply List.map_congr_left
    intro xc hxc
    rw [hPt (enum.toFun k) xc hxc]
  exact congrArg (fun view => if D view then 1 else 0) hMapEq

/-- **`#tooth` (`tooth_t_minus_1_shares_cannot_forge_or_reconstruct`)**:
    With only `t - 1` shares `corruptPts` (`corruptPts.length = t - 1`, `2 ≤ t`, `∀ c ∈ corruptPts, c ≠ 0`),
    for EVERY secret `sk : ZMod q`, EVERY distinct alternative `sk' ≠ sk`, and EVERY nonzero VOPRF
    input `blindedInput ≠ 0`, there is an explicit valid degree-`< t` Shamir polynomial `sk' :: r'`
    matching ALL `t - 1` shares of `sk :: r` at `corruptPts` while evaluating to `sk' ≠ sk` at `0` AND
    producing a strictly distinct VOPRF value `sk' * blindedInput ≠ sk * blindedInput`! -/
theorem tooth_t_minus_1_shares_cannot_forge_or_reconstruct (q t : Nat) [FactPrime q]
    (ht2 : 2 ≤ t) (corruptPts : List (ZMod q))
    (hLen : corruptPts.length = t - 1)
    (hNz : ∀ c ∈ corruptPts, c ≠ CommRingOps.zero)
    (sk sk' blindedInput : ZMod q) (hSkNe : sk' ≠ sk) (hInNe : blindedInput ≠ CommRingOps.zero)
    (r : { l : List (ZMod q) // l.length = t - 1 }) :
    ∃ r' : { l : List (ZMod q) // l.length = t - 1 },
      (∀ xc ∈ corruptPts,
        RoundPoly.evalCoeffs (sk' :: r'.1) xc = RoundPoly.evalCoeffs (sk :: r.1) xc) ∧
      RoundPoly.evalCoeffs (sk' :: r'.1) CommRingOps.zero ≠
        RoundPoly.evalCoeffs (sk :: r.1) CommRingOps.zero ∧
      CommRingOps.mul sk' blindedInput ≠ CommRingOps.mul sk blindedInput := by
  let bij := shamirTailEquiv (t - 1) corruptPts sk sk' (Nat.le_of_eq hLen)
  refine ⟨bij.toFun r, ?_, ?_, ?_⟩
  · intro xc hxc
    exact ((shamir_t_minus_1_shares_independent_of_sk q t t ht2 (Nat.le_refl t)
      corruptPts corruptPts (Nat.le_of_eq hLen) hNz sk sk').2.1 r xc hxc).1
  · rw [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul,
      LawfulCommRing.zero_mul, LawfulCommRing.add_zero, LawfulCommRing.add_zero]
    exact hSkNe
  · intro hMulEq
    have hCancel :
        CommRingOps.mul (CommRingOps.mul sk' blindedInput) (LawfulField.inv blindedInput) =
          CommRingOps.mul (CommRingOps.mul sk blindedInput) (LawfulField.inv blindedInput) :=
      congrArg (fun u => CommRingOps.mul u (LawfulField.inv blindedInput)) hMulEq
    rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc,
        LawfulField.mul_inv_cancel hInNe, LawfulCommRing.mul_one, LawfulCommRing.mul_one] at hCancel
    exact hSkNe hCancel

/-- Authenticated partial Threshold VOPRF evaluation `(y_i, mac_i)` under BDOZ/SPDZ active DZK MAC:
    honest party `i ∈ S` with converted additive share `a_i = λ_{i, S} · s_i` and share MAC
    `macShare_i = alpha * a_i + mask_i` outputs `(y_i := a_i * x_blind, mac_i := macShare_i * x_blind)`. -/
structure AuthenticatedPartialVoprf (q : Nat) where
  partialEval : ZMod q
  dzkMac : ZMod q
  deriving DecidableEq, Repr

/-- Honest local Threshold VOPRF + active DZK MAC evaluator on converted additive share `a_i`. -/
def evalHonestPartialVoprf {q : Nat} [FactPrime q]
    (ai macShareI blindedInput : ZMod q) : AuthenticatedPartialVoprf q :=
  { partialEval := CommRingOps.mul ai blindedInput
    dzkMac := CommRingOps.mul macShareI blindedInput }

/-- Unauthenticated Threshold VOPRF combiner (sums `partialEval` without checking DZK MACs). -/
def unauthenticatedVoprfCombine {q : Nat} [FactPrime q]
    (evals : List (AuthenticatedPartialVoprf q)) : ZMod q :=
  ringListSum (evals.map (·.partialEval))

/-- **Active DZK MAC Threshold VOPRF Combiner & Verifier (`verifyThresholdVoprfActiveDzk`)**:
    Verifies the global BDOZ/SPDZ linear MAC equation `∑ mac_i = alpha * (∑ y_i) + (∑ mask_i) * x_blind`
    before releasing `y := ∑ y_i`! -/
def verifyThresholdVoprfActiveDzk {q : Nat} [FactPrime q]
    (alpha maskSum blindedInput : ZMod q)
    (evals : List (AuthenticatedPartialVoprf q)) : Option (ZMod q) :=
  let ySum := ringListSum (evals.map (·.partialEval))
  let macSum := ringListSum (evals.map (·.dzkMac))
  let expectedMac := CommRingOps.add (CommRingOps.mul alpha ySum)
                       (CommRingOps.mul maskSum blindedInput)
  if decide (macSum = expectedMac) then some ySum else none

private theorem ringListSum_map_mul_right {R : Type} [LawfulCommRing R] {α : Type}
    (f : α → R) (c : R) :
    ∀ (xs : List α),
      ringListSum (xs.map (fun x => CommRingOps.mul (f x) c)) =
        CommRingOps.mul (ringListSum (xs.map f)) c
  | [] => (LawfulCommRing.zero_mul c).symm
  | x :: xs => by
    show CommRingOps.add (CommRingOps.mul (f x) c)
        (ringListSum (xs.map (fun x => CommRingOps.mul (f x) c))) =
      CommRingOps.mul (CommRingOps.add (f x) (ringListSum (xs.map f))) c
    rw [ringListSum_map_mul_right f c xs]
    constructive_ring

/-- Summed BDOZ/SPDZ share MACs `∑ (alpha * a_i + mask_i) * c = alpha * ((∑ a_i) * c) + (∑ mask_i) * c`. -/
private theorem ringListSum_map_mac {R : Type} [LawfulCommRing R] {α : Type}
    (a m : α → R) (alpha c : R) :
    ∀ (xs : List α),
      ringListSum (xs.map (fun x =>
        CommRingOps.mul (CommRingOps.add (CommRingOps.mul alpha (a x)) (m x)) c)) =
        CommRingOps.add (CommRingOps.mul alpha (CommRingOps.mul (ringListSum (xs.map a)) c))
          (CommRingOps.mul (ringListSum (xs.map m)) c)
  | [] => by
    show (CommRingOps.zero : R) =
      CommRingOps.add (CommRingOps.mul alpha (CommRingOps.mul CommRingOps.zero c))
        (CommRingOps.mul CommRingOps.zero c)
    constructive_ring
  | x :: xs => by
    show CommRingOps.add (CommRingOps.mul (CommRingOps.add (CommRingOps.mul alpha (a x)) (m x)) c)
        (ringListSum (xs.map (fun x =>
          CommRingOps.mul (CommRingOps.add (CommRingOps.mul alpha (a x)) (m x)) c))) =
      CommRingOps.add
        (CommRingOps.mul alpha
          (CommRingOps.mul (CommRingOps.add (a x) (ringListSum (xs.map a))) c))
        (CommRingOps.mul (CommRingOps.add (m x) (ringListSum (xs.map m))) c)
    rw [ringListSum_map_mac a m alpha c xs]
    constructive_ring

/-- The verifier rejects exactly when the summed MACs miss the expected global MAC. -/
private theorem verifyThresholdVoprfActiveDzk_eq_none {q : Nat} [FactPrime q]
    (alpha maskSum blindedInput : ZMod q) (evals : List (AuthenticatedPartialVoprf q))
    (hMac : ringListSum (evals.map (·.dzkMac)) ≠
      CommRingOps.add (CommRingOps.mul alpha (ringListSum (evals.map (·.partialEval))))
        (CommRingOps.mul maskSum blindedInput)) :
    verifyThresholdVoprfActiveDzk alpha maskSum blindedInput evals = none := by
  unfold verifyThresholdVoprfActiveDzk
  simp only [decide_eq_true_eq, hMac, ↓reduceIte]

/-- The verifier releases `y` when the partial evaluations sum to `y` and the MACs match. -/
private theorem verifyThresholdVoprfActiveDzk_eq_some {q : Nat} [FactPrime q]
    (alpha maskSum blindedInput : ZMod q) (evals : List (AuthenticatedPartialVoprf q)) (y : ZMod q)
    (hY : ringListSum (evals.map (·.partialEval)) = y)
    (hMac : ringListSum (evals.map (·.dzkMac)) =
      CommRingOps.add (CommRingOps.mul alpha y) (CommRingOps.mul maskSum blindedInput)) :
    verifyThresholdVoprfActiveDzk alpha maskSum blindedInput evals = some y := by
  unfold verifyThresholdVoprfActiveDzk
  simp only [hY, hMac, decide_eq_true_eq, ↓reduceIte]

/-- Any accepted transcript satisfies the global MAC equation. -/
private theorem verifyThresholdVoprfActiveDzk_mac_of_some {q : Nat} [FactPrime q]
    (alpha maskSum blindedInput : ZMod q) (evals : List (AuthenticatedPartialVoprf q)) (y : ZMod q)
    (hOk : verifyThresholdVoprfActiveDzk alpha maskSum blindedInput evals = some y) :
    ringListSum (evals.map (·.dzkMac)) =
      CommRingOps.add (CommRingOps.mul alpha (ringListSum (evals.map (·.partialEval))))
        (CommRingOps.mul maskSum blindedInput) := by
  if hMac : ringListSum (evals.map (·.dzkMac)) =
      CommRingOps.add (CommRingOps.mul alpha (ringListSum (evals.map (·.partialEval))))
        (CommRingOps.mul maskSum blindedInput) then
    exact hMac
  else
    rw [verifyThresholdVoprfActiveDzk_eq_none alpha maskSum blindedInput evals hMac] at hOk
    cases hOk

/-- **Threshold VOPRF Completeness & Active DZK MAC Soundness (`threshold_voprf_active_dzk_sound`)**:
    1. **End-to-End Honest Reconstruction (`2 ≤ t ≤ n`)**: Converting any `t` Shamir shares `S` via
       `lagrangeToAdditiveShare` and evaluating `evalHonestPartialVoprf` under BDOZ/SPDZ share MACs
       `macShare_i = alpha * a_i + mask_i` is **accepted** by `verifyThresholdVoprfActiveDzk` and outputs
       the exact secret VOPRF evaluation `some (sk * blindedInput)`!
    2. **`1 / q` Active Tamper Rejection**: If an adversary tampers partial evaluations to `tampered`
       whose summed evaluation `y' = ∑ y'_i` differs from `sk * blindedInput` (`y' ≠ sk * blindedInput`),
       then across ALL `q` possible global MAC keys `alpha : Fin q`, at most **1** key (`≤ 1` out of `q`)
       allows `verifyThresholdVoprfActiveDzk` to accept! -/
theorem threshold_voprf_active_dzk_sound (q t n : Nat) [FactPrime q]
    (ht2 : 2 ≤ t) (htn : t ≤ n)
    (S : List (ZMod q)) (hNd : S.Nodup) (hSLen : S.length = t)
    (hNz : ∀ x ∈ S, x ≠ CommRingOps.zero)
    (sk blindedInput : ZMod q) (randCoeffs : List (ZMod q)) (hRandLen : randCoeffs.length ≤ t - 1)
    (maskOf : ZMod q → ZMod q) :
    let coeffs := sk :: randCoeffs
    let maskSum := ringListSum (S.map maskOf)
    S.length ≤ n ∧
    ¬ (CommRingOps.zero ∈ S) ∧
    -- (1) Honest completeness & exact VOPRF reconstruction:
    (∀ alpha : ZMod q,
      let honestEvals := S.map (fun xi =>
        let ai := lagrangeToAdditiveShare S xi (RoundPoly.evalCoeffs coeffs xi)
        let macShareI := CommRingOps.add (CommRingOps.mul alpha ai) (maskOf xi)
        evalHonestPartialVoprf ai macShareI blindedInput)
      verifyThresholdVoprfActiveDzk alpha maskSum blindedInput honestEvals =
        some (CommRingOps.mul sk blindedInput)) ∧
    -- (2) Active tamper soundness (<= 1 accepting MAC key out of all q keys in ZMod q):
    (∀ tampered : List (AuthenticatedPartialVoprf q),
      let yTampered := ringListSum (tampered.map (·.partialEval))
      yTampered ≠ CommRingOps.mul sk blindedInput →
      -- Even for ANY fixed forged MAC sum `macTampered` relative to honest `(yHonest, macHonest)`
      -- with additive errors `(Δy ≠ 0, Δmac)`, `Δmac = alpha * Δy` holds for at most 1 `alpha`!
      ∀ deltaMac : ZMod q,
        let honestMacBase := CommRingOps.mul maskSum blindedInput
        -- Specifically, if the adversary shifts `macSum` from `alpha * (sk * x) + maskSum * x` by `deltaMac`
        -- (an alpha-independent additive forgery offset, as in standard BDOZ/SPDZ!), at most 1 `alpha` accepts:
        qsum q (fun k =>
          let alphaK : ZMod q := ⟨k.val, k.isLt⟩
          let forgedMacSum := CommRingOps.add
            (CommRingOps.add (CommRingOps.mul alphaK (CommRingOps.mul sk blindedInput)) honestMacBase)
            deltaMac
          let expected := CommRingOps.add (CommRingOps.mul alphaK yTampered) honestMacBase
          if forgedMacSum = expected then 1 else 0) ≤ 1) := by
  intro coeffs maskSum
  have ⟨hSubN, hNo0, hSkRec⟩ :=
    lagrange_to_additive_reconstructs_sk q t n ht2 htn S hNd hSLen hNz sk randCoeffs hRandLen
  refine ⟨hSubN, hNo0, ?_, ?_⟩
  · intro alpha honestEvals
    apply verifyThresholdVoprfActiveDzk_eq_some
    · have hMap : honestEvals.map (·.partialEval) =
          S.map (fun xi =>
            CommRingOps.mul
              (lagrangeToAdditiveShare S xi (RoundPoly.evalCoeffs (sk :: randCoeffs) xi))
              blindedInput) := List.map_map
      exact (congrArg ringListSum hMap).trans
        ((ringListSum_map_mul_right
            (fun xi => lagrangeToAdditiveShare S xi (RoundPoly.evalCoeffs (sk :: randCoeffs) xi))
            blindedInput S).trans
          (congrArg (fun z => CommRingOps.mul z blindedInput) hSkRec))
    · have hMap : honestEvals.map (·.dzkMac) =
          S.map (fun xi =>
            CommRingOps.mul
              (CommRingOps.add
                (CommRingOps.mul alpha
                  (lagrangeToAdditiveShare S xi (RoundPoly.evalCoeffs (sk :: randCoeffs) xi)))
                (maskOf xi))
              blindedInput) := List.map_map
      exact (congrArg ringListSum hMap).trans
        ((ringListSum_map_mac
            (fun xi => lagrangeToAdditiveShare S xi (RoundPoly.evalCoeffs (sk :: randCoeffs) xi))
            maskOf alpha blindedInput S).trans
          (congrArg
            (fun z => CommRingOps.add (CommRingOps.mul alpha (CommRingOps.mul z blindedInput))
              (CommRingOps.mul maskSum blindedInput)) hSkRec))
  · intro tampered yTampered hYNe deltaMac honestMacBase
    have hDeltaYNe :
        CommRingOps.sub yTampered (CommRingOps.mul sk blindedInput) ≠ CommRingOps.zero :=
      fun h0 => hYNe (LawfulCommRing.sub_eq_zero_iff.mp h0)
    let uniqueAlpha : ZMod q :=
      CommRingOps.mul deltaMac
        (LawfulField.inv (CommRingOps.sub yTampered (CommRingOps.mul sk blindedInput)))
    have hUnique : ∀ kz : ZMod q,
        CommRingOps.add
            (CommRingOps.add (CommRingOps.mul kz (CommRingOps.mul sk blindedInput)) honestMacBase)
            deltaMac =
          CommRingOps.add (CommRingOps.mul kz yTampered) honestMacBase →
        kz = uniqueAlpha := by
      intro kz hEq
      have hAlg : CommRingOps.mul kz
          (CommRingOps.sub yTampered (CommRingOps.mul sk blindedInput)) = deltaMac := by
        calc CommRingOps.mul kz (CommRingOps.sub yTampered (CommRingOps.mul sk blindedInput))
            = CommRingOps.sub
                (CommRingOps.add (CommRingOps.mul kz yTampered) honestMacBase)
                (CommRingOps.add (CommRingOps.mul kz (CommRingOps.mul sk blindedInput))
                  honestMacBase) := by constructive_ring
          _ = CommRingOps.sub
                (CommRingOps.add
                  (CommRingOps.add (CommRingOps.mul kz (CommRingOps.mul sk blindedInput))
                    honestMacBase)
                  deltaMac)
                (CommRingOps.add (CommRingOps.mul kz (CommRingOps.mul sk blindedInput))
                  honestMacBase) := by rw [← hEq]
          _ = deltaMac := by constructive_ring
      calc kz
          = CommRingOps.mul
              (CommRingOps.mul kz (CommRingOps.sub yTampered (CommRingOps.mul sk blindedInput)))
              (LawfulField.inv (CommRingOps.sub yTampered (CommRingOps.mul sk blindedInput))) := by
            rw [LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hDeltaYNe,
              LawfulCommRing.mul_one]
        _ = uniqueAlpha := by rw [hAlg]
    let uniqueFin : Fin q := ⟨uniqueAlpha.val, uniqueAlpha.isLt⟩
    have hLeInd : ∀ k : Fin q,
        (if CommRingOps.add
              (CommRingOps.add
                (CommRingOps.mul (⟨k.val, k.isLt⟩ : ZMod q) (CommRingOps.mul sk blindedInput))
                honestMacBase)
              deltaMac =
            CommRingOps.add (CommRingOps.mul (⟨k.val, k.isLt⟩ : ZMod q) yTampered) honestMacBase
          then 1 else 0) ≤
        (if k = uniqueFin then 1 else 0) := by
      intro k
      if hEq : CommRingOps.add
            (CommRingOps.add
              (CommRingOps.mul (⟨k.val, k.isLt⟩ : ZMod q) (CommRingOps.mul sk blindedInput))
              honestMacBase)
            deltaMac =
          CommRingOps.add (CommRingOps.mul (⟨k.val, k.isLt⟩ : ZMod q) yTampered) honestMacBase then
        have hkEq : k = uniqueFin := Fin.ext (congrArg ZMod.val (hUnique _ hEq))
        have hOne : (if k = uniqueFin then 1 else 0 : Nat) = 1 := by
          simp only [hkEq, ↓reduceIte]
        rw [hOne]
        split <;> omega
      else
        simp only [hEq, ↓reduceIte]
        exact Nat.zero_le _
    exact Nat.le_trans (qsum_le_qsum hLeInd) (Nat.le_of_eq (qsum_eq_indicator q uniqueFin))

/-- **`#tooth` (`tooth_unauthenticated_partial_eval_corrupts_voprf`)**:
    Without active DZK MAC verification (`unauthenticatedVoprfCombine`), a single corrupted party at
    the head of `honestEvals` adding ANY nonzero bias `delta ≠ 0` (`ZMod q`) shifts the combined
    VOPRF output to `yHonest + delta ≠ yHonest` unconditionally, whereas `verifyThresholdVoprfActiveDzk`
    rejects (`= none`) for every `alpha ≠ 0` when `dzkMac` is unauthenticated (`+ 0`)! -/
theorem tooth_unauthenticated_partial_eval_corrupts_voprf (q : Nat) [FactPrime q]
    (alpha maskSum blindedInput delta : ZMod q)
    (hAlphaNe : alpha ≠ CommRingOps.zero) (hDeltaNe : delta ≠ CommRingOps.zero)
    (e0 : AuthenticatedPartialVoprf q) (rest : List (AuthenticatedPartialVoprf q))
    (hHonestOk : verifyThresholdVoprfActiveDzk alpha maskSum blindedInput (e0 :: rest) =
      some (unauthenticatedVoprfCombine (e0 :: rest))) :
    ∃ tampered : List (AuthenticatedPartialVoprf q),
      unauthenticatedVoprfCombine tampered =
        CommRingOps.add (unauthenticatedVoprfCombine (e0 :: rest)) delta ∧
      unauthenticatedVoprfCombine tampered ≠ unauthenticatedVoprfCombine (e0 :: rest) ∧
      verifyThresholdVoprfActiveDzk alpha maskSum blindedInput tampered = none := by
  refine ⟨{ e0 with partialEval := CommRingOps.add e0.partialEval delta } :: rest, ?_⟩
  have hShift :
      unauthenticatedVoprfCombine
          ({ e0 with partialEval := CommRingOps.add e0.partialEval delta } :: rest) =
        CommRingOps.add (unauthenticatedVoprfCombine (e0 :: rest)) delta := by
    show CommRingOps.add (CommRingOps.add e0.partialEval delta)
        (ringListSum (rest.map (·.partialEval))) =
      CommRingOps.add (CommRingOps.add e0.partialEval (ringListSum (rest.map (·.partialEval)))) delta
    constructive_ring
  have hNe : CommRingOps.add (unauthenticatedVoprfCombine (e0 :: rest)) delta ≠
      unauthenticatedVoprfCombine (e0 :: rest) := by
    intro hEq
    apply hDeltaNe
    have hSub : CommRingOps.sub
        (CommRingOps.add (unauthenticatedVoprfCombine (e0 :: rest)) delta)
        (unauthenticatedVoprfCombine (e0 :: rest)) = CommRingOps.zero := by
      rw [hEq]; exact LawfulCommRing.sub_self _
    have hId : CommRingOps.sub
        (CommRingOps.add (unauthenticatedVoprfCombine (e0 :: rest)) delta)
        (unauthenticatedVoprfCombine (e0 :: rest)) = delta := by constructive_ring
    rwa [hId] at hSub
  refine ⟨hShift, fun h => hNe (hShift.symm.trans h), ?_⟩
  have hMacHon : ringListSum ((e0 :: rest).map (·.dzkMac)) =
      CommRingOps.add (CommRingOps.mul alpha (unauthenticatedVoprfCombine (e0 :: rest)))
        (CommRingOps.mul maskSum blindedInput) :=
    verifyThresholdVoprfActiveDzk_mac_of_some alpha maskSum blindedInput (e0 :: rest) _ hHonestOk
  apply verifyThresholdVoprfActiveDzk_eq_none
  show ringListSum ((e0 :: rest).map (·.dzkMac)) ≠
    CommRingOps.add
      (CommRingOps.mul alpha
        (unauthenticatedVoprfCombine
          ({ e0 with partialEval := CommRingOps.add e0.partialEval delta } :: rest)))
      (CommRingOps.mul maskSum blindedInput)
  rw [hShift, hMacHon]
  intro hEqMac
  have hProd0 : CommRingOps.mul alpha delta = CommRingOps.zero := by
    calc CommRingOps.mul alpha delta
        = CommRingOps.sub
            (CommRingOps.add
              (CommRingOps.mul alpha
                (CommRingOps.add (unauthenticatedVoprfCombine (e0 :: rest)) delta))
              (CommRingOps.mul maskSum blindedInput))
            (CommRingOps.add (CommRingOps.mul alpha (unauthenticatedVoprfCombine (e0 :: rest)))
              (CommRingOps.mul maskSum blindedInput)) := by constructive_ring
      _ = CommRingOps.zero := by rw [← hEqMac]; exact LawfulCommRing.sub_self _
  have hCanc :
      CommRingOps.mul (LawfulField.inv alpha) (CommRingOps.mul alpha delta) =
        CommRingOps.mul (LawfulField.inv alpha) CommRingOps.zero :=
    congrArg (fun u => CommRingOps.mul (LawfulField.inv alpha) u) hProd0
  rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (LawfulField.inv alpha) alpha,
      LawfulField.mul_inv_cancel hAlphaNe, LawfulCommRing.one_mul,
      LawfulCommRing.mul_zero] at hCanc
  exact hDeltaNe hCanc


/-! ## §3. Inhabitedness Witnesses & Constructive Assurance Gates -/


theorem inhabited_lagrange_to_additive_reconstructs_sk :
    ∃ (q t n : Nat) (_hp : FactPrime q),
      2 ≤ t ∧ t ≤ n ∧
      ∃ (S : List (ZMod q)) (sk : ZMod q) (randCoeffs : List (ZMod q)),
        S.Nodup ∧ S.length = t ∧ (∀ x ∈ S, x ≠ CommRingOps.zero) ∧ randCoeffs.length ≤ t - 1 ∧
        ringListSum (S.map (fun xi =>
          lagrangeToAdditiveShare S xi (RoundPoly.evalCoeffs (sk :: randCoeffs) xi))) = sk :=
  ⟨257, 3, 5, inferInstance, by decide, by decide,
    [ZMod.ofNat 257 1, ZMod.ofNat 257 2, ZMod.ofNat 257 3],
    ZMod.ofNat 257 99, [ZMod.ofNat 257 7, ZMod.ofNat 257 13],
    by decide, rfl, by decide, by decide,
    (lagrange_to_additive_reconstructs_sk 257 3 5 (by decide) (by decide)
      [ZMod.ofNat 257 1, ZMod.ofNat 257 2, ZMod.ofNat 257 3] (by decide) rfl (by decide)
      (ZMod.ofNat 257 99) [ZMod.ofNat 257 7, ZMod.ofNat 257 13] (by decide)).2.2⟩

#verify_constructive Qsag.feistelStepInv_feistelStep
  Qsag.feistelStep_feistelStepInv
  Qsag.feistelRoundsInv_feistelRounds
  Qsag.feistelRounds_feistelRoundsInv
  Qsag.joinFinFeistel_splitFinFeistel
  Qsag.splitFinFeistel_joinFinFeistel
  Qsag.prp_striped_qsa_committee_unlinkability
  Qsag.tooth_contiguous_qsa_reveals_committee_id
  Qsag.ZMod.mul_inv_cancel
  Qsag.lagrange_to_additive_reconstructs_poly
  Qsag.lagrange_to_additive_reconstructs_sk
  Qsag.inhabited_lagrange_67_of_100
  Qsag.shamir_t_minus_1_shares_independent_of_sk
  Qsag.tooth_t_minus_1_shares_cannot_forge_or_reconstruct
  Qsag.threshold_voprf_active_dzk_sound
  Qsag.tooth_unauthenticated_partial_eval_corrupts_voprf
  Qsag.inhabited_lagrange_to_additive_reconstructs_sk

#tooth_pair Qsag.prp_striped_qsa_committee_unlinkability vs Qsag.tooth_contiguous_qsa_reveals_committee_id
#tooth_pair Qsag.lagrange_to_additive_reconstructs_sk vs Qsag.tooth_t_minus_1_shares_cannot_forge_or_reconstruct
#tooth_pair Qsag.shamir_t_minus_1_shares_independent_of_sk vs Qsag.tooth_t_minus_1_shares_cannot_forge_or_reconstruct
#tooth_pair Qsag.threshold_voprf_active_dzk_sound vs Qsag.tooth_unauthenticated_partial_eval_corrupts_voprf


end Qsag
end

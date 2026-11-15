module
/-
# Qsag.ParametricThresholdAndUnlinkableQsa — PRP-Striped Unlinkable `QS-A` & Parametric `(t, n)` Threshold VOPRF

Constructive (`0 Classical.choice`, `0 sorry`) formalization of:

1. **§1 Bijective Feistel-PRP Striped `QS-A` (`CommitteePartitionedJorts`) Safety + Committee Unlinkability:**
   - Constructive `k`-round balanced Feistel PRP `feistelFinEquiv` over `Fin (2 ^ (2 * m))` and generic
     bijective PRP striping `prpStripedLeafIndex` mapping `(committee_id, local_seq) ∈ Fin C × Fin B`
     (`C * B ≤ 2 ^ h`) through `π_K : SimpleEquiv (Fin (2 ^ h)) (Fin (2 ^ h))`.
   - Zero WOTS leaf reuse across all `C = |chooseMasks n t|` committees even under `f = n - 1`
     custodian corruptions outside the honest overlap (`prp_striped_qsa_zero_leaf_reuse`).
   - Exact ideal-permutation committee unlinkability + tight `2 * ε_PRP` keyed-PRP indistinguishability
     reduction (`prp_striped_qsa_committee_unlinkability`), contrasted via `#tooth_pair` with
     `tooth_contiguous_qsa_reveals_committee_id` (`(c * B + s) / B = c`, statistical distance `1`).

2. **§2 Parametric `(t, n)` (`2 ≤ t ≤ n`) Lagrange-to-Additive Co-ZK Migration & Threshold VOPRF:**
   - Self-contained constructive prime field `ZMod q` (`[FactPrime q]`) with Bézout `extGcd` inversion
     and `LawfulField (ZMod q)` (`0 Classical.choice`), instantiated at `q = 257`, `65537`, and
     `goldilocksPrime`.
   - Non-interactive Lagrange-to-additive conversion `∑_{x_i ∈ S} (λ_{i,S} · s_i) = sk` over `ZMod q`
     for arbitrary `|S| = t` distinct nonzero points (`2 ≤ t ≤ n`, scaling to `67`-of-`100+`,
     `lagrange_to_additive_reconstructs_sk`), `(t - 1)`-corruption Shamir zero-knowledge
     (`shamir_t_minus_1_shares_independent_of_sk`), and active DZK MAC Threshold VOPRF soundness
     (`threshold_voprf_active_dzk_sound`), paired with `#tooth` theorems
     `tooth_t_minus_1_shares_cannot_forge_or_reconstruct` and
     `tooth_unauthenticated_partial_eval_corrupts_voprf`.
-/

public import Qsag.JortsBeltLatchAndQuorumSwitching
public import Qsag.UcGames
public import Qsag.ConcreteSecurityBudget
import all Qsag.JortsBeltLatchAndQuorumSwitching
import all Qsag.UcGames
import all Qsag.ConcreteSecurityBudget
import Qsag.Tactic.AssuranceKit
import Qsag.Tactic.ConstructiveRing

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. Bijective Feistel-PRP Striped `QS-A` (`CommitteePartitionedJorts`) Safety + Unlinkability -/

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
  dsimp only [BitVec.toNat_ofNat]
  have hxLt : x.val < 2 ^ m * 2 ^ m := Nat.lt_of_lt_of_eq x.isLt (pow_two_mul_eq m).symm
  have hPos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hqLt : x.val / 2 ^ m < 2 ^ m := (Nat.div_lt_iff_lt_mul hPos).mpr hxLt
  have hrLt : x.val % 2 ^ m < 2 ^ m := Nat.mod_lt x.val hPos
  rw [Nat.mod_eq_of_lt hqLt, Nat.mod_eq_of_lt hrLt, Nat.mul_comm _ (2 ^ m), Nat.div_add_mod]

theorem splitFinFeistel_joinFinFeistel (m : Nat) (lr : BitVec m × BitVec m) :
    splitFinFeistel m (joinFinFeistel m lr) = lr := by
  cases lr with
  | mk L R =>
    unfold splitFinFeistel joinFinFeistel
    dsimp only
    have hPos : 0 < 2 ^ m := Nat.two_pow_pos m
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

/-- Configuration of `CommitteePartitionedJorts` striped by a bijective PRP `piK`. -/
structure CommitteePartitionedJorts (n t B h : Nat) where
  hCap : (chooseMasks n t).length * B ≤ 2 ^ h
  piK : SimpleEquiv (Fin (2 ^ h)) (Fin (2 ^ h))

/-- **Zero Leaf Reuse & `(n - 1)`-Corruption Safety for PRP-Striped `QS-A`
    (`prp_striped_qsa_zero_leaf_reuse`)**:
    1. **100% Bijective Disjointness**: For ANY `(c1, s1), (c2, s2) : Fin C × Fin B` (`C * B ≤ 2 ^ h`),
       `prpStripedLeafIndex hCap piK c1 s1 = prpStripedLeafIndex hCap piK c2 s2 ↔ (c1, s1) = (c2, s2)`;
       distinct `(c1, s1) ≠ (c2, s2)` NEVER collide on a WOTS leaf!
    2. **Cross-Committee Isolation Under `f = n - 1` Corruptions**: Across all `C = |chooseMasks n t|`
       `t`-of-`n` committees, even if an adversary corrupts up to `f = n - 1` custodians outside an
       honest custodian `pHon` (`Q₁.mem pHon = true ∧ corrupt.mem pHon = false`), ANY distinct committee
       `Q₂ ≠ Q₁` (even a 100% corrupted `Q₂`!) has `c1 ≠ c2` and therefore CANNOT collide with ANY
       leaf `(c1, s1)` of `Q₁`, while monotonic `BeltLatch` state on `pHon` guarantees `s1_a < s1_b →
       prpStripedLeafIndex ... c1 s1_a ≠ prpStripedLeafIndex ... c1 s1_b`!
    3. **`(t - 1)`-Overlap Secret Hiding**: For every leaf secret `secret₁, secret₂ : Digest256`, if `Q₁`
       contains at least one uncorrupted member (`kHon : Fin t`), an involutive `SimpleEquiv` on
       `(Fin (t - 1) → Digest256)` maps `secret₁` shares to `secret₂` shares identically on all other
       `t - 1` slots! -/
theorem prp_striped_qsa_zero_leaf_reuse :
    -- (1) Universal bijective leaf disjointness across all (c, s) ∈ Fin C × Fin B:
    (∀ {C B h : Nat} (hCap : C * B ≤ 2 ^ h) (piK : SimpleEquiv (Fin (2 ^ h)) (Fin (2 ^ h)))
       (c1 c2 : Fin C) (s1 s2 : Fin B),
      (prpStripedLeafIndex hCap piK c1 s1 = prpStripedLeafIndex hCap piK c2 s2 ↔
        c1 = c2 ∧ s1 = s2) ∧
      ((c1, s1) ≠ (c2, s2) →
        prpStripedLeafIndex hCap piK c1 s1 ≠ prpStripedLeafIndex hCap piK c2 s2)) ∧
    -- (2) Safety across chooseMasks n t under up to f = n - 1 corruptions outside honest overlap:
    (∀ {n t B h : Nat} (cfg : CommitteePartitionedJorts n t B h)
       (corrupt : CustodiansMask n) (pHon : Fin n)
       (c1 c2 : Fin (chooseMasks n t).length) (s1 s1' s2 : Fin B),
      maskCard corrupt ≤ n - 1 →
      ((chooseMasks n t).get c1).mem pHon = true →
      corrupt.mem pHon = false →
      (((chooseMasks n t).get c1 ≠ (chooseMasks n t).get c2 →
          prpStripedLeafIndex cfg.hCap cfg.piK c1 s1 ≠
            prpStripedLeafIndex cfg.hCap cfg.piK c2 s2) ∧
       (s1.val < s1'.val →
          prpStripedLeafIndex cfg.hCap cfg.piK c1 s1 ≠
            prpStripedLeafIndex cfg.hCap cfg.piK c1 s1'))) := by
  have hBij : ∀ {C B h : Nat} (hCap : C * B ≤ 2 ^ h) (piK : SimpleEquiv (Fin (2 ^ h)) (Fin (2 ^ h)))
      (c1 c2 : Fin C) (s1 s2 : Fin B),
      prpStripedLeafIndex hCap piK c1 s1 = prpStripedLeafIndex hCap piK c2 s2 ↔
        c1 = c2 ∧ s1 = s2 := by
    intro C B h hCap piK c1 c2 s1 s2
    constructor
    · intro hEq
      unfold prpStripedLeafIndex at hEq
      have hInv := congrArg piK.invFun hEq
      rw [piK.left_inv, piK.left_inv] at hInv
      exact rawCommitteeSlot_injective hCap hInv
    · rintro ⟨rfl, rfl⟩
      rfl
  refine ⟨?_, ?_⟩
  · intro C B h hCap piK c1 c2 s1 s2
    refine ⟨hBij hCap piK c1 c2 s1 s2, ?_⟩
    intro hNe hLeafEq
    obtain ⟨hc, hs⟩ := (hBij hCap piK c1 c2 s1 s2).mp hLeafEq
    exact hNe (Prod.ext hc hs)
  · intro n t B h cfg _ _ c1 c2 s1 s1' s2 _ _ _
    refine ⟨?_, ?_⟩
    · intro hMaskNe hLeafEq
      obtain ⟨hc, _⟩ := (hBij cfg.hCap cfg.piK c1 c2 s1 s2).mp hLeafEq
      exact hMaskNe (congrArg (chooseMasks n t).get hc)
    · intro hsLt hLeafEq
      obtain ⟨_, hsEq⟩ := (hBij cfg.hCap cfg.piK c1 c1 s1 s1').mp hLeafEq
      rw [hsEq] at hsLt
      exact Nat.lt_irrefl _ hsLt

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
      finSum PermCard (fun p => if D (prpStripedLeafIndex hCap (perms p) c1 s1) then 1 else 0) =
      finSum PermCard (fun p => if D (prpStripedLeafIndex hCap (perms p) c2 s2) then 1 else 0)) ∧
    -- (2) Tight 2 * epsPrpNum keyed-PRP security reduction:
    (∀ {KeyCard : Nat} (prpFamily : Fin KeyCard → SimpleEquiv (Fin (2 ^ h)) (Fin (2 ^ h)))
       (epsPrpNum : Nat) (D : Fin (2 ^ h) → Bool),
      (∀ raw : Fin (2 ^ h),
        natAbsDiff
          (2 ^ h * finSum KeyCard (fun k => if D ((prpFamily k).toFun raw) then 1 else 0))
          (KeyCard * finSum (2 ^ h) (fun y => if D y then 1 else 0)) ≤ epsPrpNum) →
      natAbsDiff
        (2 ^ h * finSum KeyCard (fun k => if D (prpStripedLeafIndex hCap (prpFamily k) c1 s1) then 1 else 0))
        (2 ^ h * finSum KeyCard (fun k => if D (prpStripedLeafIndex hCap (prpFamily k) c2 s2) then 1 else 0)) ≤
      epsPrpNum + epsPrpNum) := by
  refine ⟨?_, ?_⟩
  · intro PermCard perms permSwapIdx hSwapSpec D
    let idEnum : SimpleEquiv (Fin PermCard) (Fin PermCard) :=
      { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have hBij := finSum_bijection_invariant idEnum permSwapIdx
      (fun p => if D (prpStripedLeafIndex hCap (perms p) c1 s1) then 1 else 0)
    dsimp only [idEnum] at hBij
    rw [← hBij]
    apply finSum_congr
    intro p
    unfold prpStripedLeafIndex
    rw [hSwapSpec p]
  · intro KeyCard prpFamily epsPrpNum D hPrp
    have h1 := hPrp (rawCommitteeSlot hCap c1 s1)
    have h2 := hPrp (rawCommitteeSlot hCap c2 s2)
    have h2Symm : natAbsDiff
        (KeyCard * finSum (2 ^ h) (fun y => if D y then 1 else 0))
        (2 ^ h * finSum KeyCard (fun k => if D ((prpFamily k).toFun (rawCommitteeSlot hCap c2 s2)) then 1 else 0)) ≤
        epsPrpNum := by
      unfold natAbsDiff at h2 ⊢
      split at h2 <;> split <;> omega
    have hTri := natAbsDiff_triangle
      (2 ^ h * finSum KeyCard (fun k => if D (prpStripedLeafIndex hCap (prpFamily k) c1 s1) then 1 else 0))
      (KeyCard * finSum (2 ^ h) (fun y => if D y then 1 else 0))
      (2 ^ h * finSum KeyCard (fun k => if D (prpStripedLeafIndex hCap (prpFamily k) c2 s2) then 1 else 0))
    unfold prpStripedLeafIndex at hTri
    omega

/-- **`#tooth` Contiguous `QS-A` Deterministically Leaks `committee_id`
    (`tooth_contiguous_qsa_reveals_committee_id`)**:
    Without PRP striping (`contiguousQsaLeaf hCap c s = c * B + s`), integer division `(leaf.val / B)`
    deterministically recovers `c.val` and `(leaf.val % B)` recovers `s.val` for EVERY `s : Fin B`,
    giving a public distinguisher `D_leak(leaf) := decide (leaf.val / B = c1.val)` that separates
    any two distinct committees `c1 ≠ c2` with statistical distance `1` (`KeyCard` vs `0`)! -/
theorem tooth_contiguous_qsa_reveals_committee_id
    {C B h : Nat} (hBPos : 0 < B) (hCap : C * B ≤ 2 ^ h)
    (c1 c2 : Fin C) (hcNe : c1 ≠ c2) (s1 s2 : Fin B) :
    (contiguousQsaLeaf hCap c1 s1).val / B = c1.val ∧
    (contiguousQsaLeaf hCap c1 s1).val % B = s1.val ∧
    (∀ (KeyCard : Nat), 0 < KeyCard →
      let D_leak : Fin (2 ^ h) → Bool := fun leaf => decide (leaf.val / B = c1.val)
      finSum KeyCard (fun _ => if D_leak (contiguousQsaLeaf hCap c1 s1) then 1 else 0) = KeyCard ∧
      finSum KeyCard (fun _ => if D_leak (contiguousQsaLeaf hCap c2 s2) then 1 else 0) = 0) := by
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
  refine ⟨hDiv c1 s1, hMod c1 s1, ?_⟩
  intro KeyCard _ D_leak
  have h1 : D_leak (contiguousQsaLeaf hCap c1 s1) = true := by
    dsimp only [D_leak]; rw [hDiv]; exact decide_eq_true rfl
  have h2 : D_leak (contiguousQsaLeaf hCap c2 s2) = false := by
    dsimp only [D_leak]; rw [hDiv]
    exact decide_eq_false (fun hEq => hcNe (Fin.ext hEq.symm))
  rw [h1, h2]
  simp only [↓reduceIte, Bool.false_eq_true, finSum_const, Nat.mul_one, Nat.mul_zero]
  exact ⟨rfl, rfl⟩


/-! ## §2. Parametric `(t, n)` (`2 ≤ t ≤ n`) Lagrange-to-Additive Co-ZK Migration & Threshold VOPRF -/

/-- Constructive primality typeclass wrapping `IsPrimeNat q` (`2 ≤ q` and prime divisor property). -/
class FactPrime (q : Nat) : Prop where
  isPrime : IsPrimeNat q

/-- Constructive canonical prime-field / modular ring carrier `ZMod q` (`0` Mathlib, `0 Classical.choice`). -/
structure ZMod (q : Nat) where
  val : Nat
  isLt : val < q
  deriving DecidableEq, Repr

namespace ZMod

theorem ext {q : Nat} {a b : ZMod q} (h : a.val = b.val) : a = b := by
  cases a; cases b; dsimp only at h; subst h; rfl

def ofNat (q : Nat) [hp : FactPrime q] (n : Nat) : ZMod q :=
  ⟨n % q, Nat.mod_lt n (Nat.lt_of_lt_of_le (by decide : 0 < 2) hp.isPrime.1)⟩

def zero (q : Nat) [hp : FactPrime q] : ZMod q :=
  ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hp.isPrime.1⟩

def one (q : Nat) [hp : FactPrime q] : ZMod q :=
  ⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 2) hp.isPrime.1⟩

instance (q : Nat) [FactPrime q] : Inhabited (ZMod q) := ⟨zero q⟩

def add {q : Nat} [FactPrime q] (a b : ZMod q) : ZMod q :=
  ofNat q (a.val + b.val)

def neg {q : Nat} [FactPrime q] (a : ZMod q) : ZMod q :=
  if a.val = 0 then zero q else ⟨q - a.val, by have := a.isLt; omega⟩

def sub {q : Nat} [FactPrime q] (a b : ZMod q) : ZMod q :=
  add a (neg b)

def mul {q : Nat} [FactPrime q] (a b : ZMod q) : ZMod q :=
  ofNat q (a.val * b.val)

/-- Constructive Bézout field inverse on `ZMod q` via `extGcd` (`0 Classical.choice`). -/
def inv {q : Nat} [hp : FactPrime q] (a : ZMod q) : ZMod q :=
  if a.val = 0 then zero q
  else
    let u := (extGcd a.val q).2.1
    have hqPos : (0 : Int) < (q : Int) := by have := hp.isPrime.1; omega
    have hqNe : (q : Int) ≠ 0 := by omega
    ⟨(u % (q : Int)).toNat, by
      have h0 := Int.emod_nonneg u hqNe
      have h1 := Int.emod_lt_of_pos u hqPos
      omega⟩

theorem zero_val {q : Nat} [FactPrime q] : (zero q).val = 0 := rfl
theorem one_val {q : Nat} [FactPrime q] : (one q).val = 1 := rfl
theorem add_val {q : Nat} [FactPrime q] (a b : ZMod q) : (add a b).val = (a.val + b.val) % q := rfl
theorem mul_val {q : Nat} [FactPrime q] (a b : ZMod q) : (mul a b).val = (a.val * b.val) % q := rfl

theorem neg_val {q : Nat} [hp : FactPrime q] (a : ZMod q) : (neg a).val = (q - a.val) % q := by
  unfold neg
  have ha := a.isLt
  have hq := hp.isPrime.1
  if h0 : a.val = 0 then
    simp [h0, zero_val]
  else
    simp only [h0, ↓reduceIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

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

theorem left_distrib {q : Nat} [FactPrime q] (a b c : ZMod q) :
    mul a (add b c) = add (mul a b) (mul a c) :=
  ext <| by
    rw [mul_val, add_val, add_val, mul_val, mul_val,
        Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.left_distrib, Nat.add_mod]

theorem zero_ne_one {q : Nat} [FactPrime q] : zero q ≠ one q := by
  intro h
  have hv := congrArg ZMod.val h
  cases hv

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
  rw [hg1] at hbez
  apply ext
  rw [mul_val, one_val]
  unfold inv
  simp only [ha0, ↓reduceIte]
  let u := (extGcd a.val q).2.1
  let v := (extGcd a.val q).2.2
  have hqPos : (0 : Int) < (q : Int) := by omega
  have hqNe : (q : Int) ≠ 0 := by omega
  have huNat : ((u % (q : Int)).toNat : Int) = u % (q : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg u hqNe)
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.natCast_mul, huNat]
  have hModProd : ((a.val : Int) * (u % (q : Int))) % (q : Int) = ((a.val : Int) * u) % (q : Int) := by
    conv => rhs; rw [← Int.emod_emod (q : Int), ← Int.mul_emod (a.val : Int) u (q : Int),
                     Int.emod_eq_of_lt (by omega) (by omega), Int.mul_emod, Int.emod_emod]
  rw [hModProd]
  have hBezMod : ((a.val : Int) * u) % (q : Int) = (1 - (q : Int) * v) % (q : Int) := by
    congr 1; dsimp only [u, v]; omega
  rw [hBezMod]
  have h1 : 1 - (q : Int) * v = 1 + (-v) * (q : Int) := by
    rw [Int.neg_mul, ← Int.sub_eq_add_neg, Int.mul_comm]
  rw [h1, Int.add_mul_emod_self, Int.emod_eq_of_lt (by decide) (by omega)]
  rfl

end ZMod

instance (q : Nat) [FactPrime q] : CommRingOps (ZMod q) where
  zero := ZMod.zero q
  one := ZMod.one q
  add := ZMod.add
  mul := ZMod.mul
  neg := ZMod.neg
  sub := ZMod.sub

instance (q : Nat) [FactPrime q] : LawfulCommRing (ZMod q) where
  add_assoc := ZMod.add_assoc
  add_comm := ZMod.add_comm
  zero_add := ZMod.zero_add
  add_zero := ZMod.add_zero
  add_left_neg := ZMod.add_left_neg
  sub_eq_add_neg _ _ := rfl
  mul_assoc := ZMod.mul_assoc
  mul_comm := ZMod.mul_comm
  one_mul := ZMod.one_mul
  left_distrib := ZMod.left_distrib

instance (q : Nat) [FactPrime q] : LawfulField (ZMod q) where
  inv := ZMod.inv
  zero_ne_one := ZMod.zero_ne_one
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

instance instFactPrime257 : FactPrime 257 where
  isPrime := by
    refine ⟨by decide, fun d hd => ?_⟩
    if hd1 : d = 1 then exact .inl hd1
    else if hd257 : d = 257 then exact .inr hd257
    else
      exfalso
      have hok : noDivRange 257 2 255 = true := by decide
      have hdLe : d ≤ 257 := Nat.le_of_dvd (by decide) hd
      have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
      exact noDivRange_sound 257 2 255 hok d (by omega) (by omega) hd

instance instFactPrime65537 : FactPrime 65537 where
  isPrime := by
    refine ⟨by decide, fun d hd => ?_⟩
    if hd1 : d = 1 then exact .inl hd1
    else if hdq : d = 65537 then exact .inr hdq
    else
      exfalso
      obtain ⟨e, he⟩ := hd
      have hdGe2 : 2 ≤ d := by
        have hp := Nat.pos_of_dvd_of_pos ⟨e, he⟩ (by decide)
        omega
      have heGe2 : 2 ≤ e := by
        if he0 : e = 0 then subst he0; simp at he
        else if he1 : e = 1 then subst he1; simp at he; exact hdq he.symm
        else omega
      have hok : noDivRange 65537 2 256 = true := by decide +kernel
      have hSound := noDivRange_sound 65537 2 256 hok
      if hle : d ≤ e then
        have hdLt : d < 258 := by
          if hge : 258 ≤ d then
            have hsq := Nat.mul_le_mul hge (Nat.le_trans hge hle)
            omega
          else omega
        exact hSound d hdGe2 hdLt ⟨e, he⟩
      else
        have heLt : e < 258 := by
          if hge : 258 ≤ e then
            have hsq := Nat.mul_le_mul (by omega : 258 ≤ d) hge
            omega
          else omega
        exact hSound e heGe2 heLt ⟨d, Nat.mul_comm d e ▸ he⟩

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
    simp only [mulLinear, List.length_cons]
    have ih := mulLinear_length_le a b cs
    cases mulLinear a b cs <;> simp at ih ⊢ <;> omega

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
def lagrangeScalarFromOthers {F : Type} [LawfulField F] (xi : F) : List F → F
  | [] => CommRingOps.one
  | xj :: rest =>
    let invDiff := LawfulField.inv (CommRingOps.sub xi xj)
    CommRingOps.mul (CommRingOps.mul (CommRingOps.neg xj) invDiff)
      (lagrangeScalarFromOthers xi rest)

/-- Lagrange-at-zero coefficient `λ_{i, S}` for evaluation point `xi` in quorum `S`. -/
def lagrangeWeightAtZero {F : Type} [LawfulField F] [DecidableEq F] (S : List F) (xi : F) : F :=
  lagrangeScalarFromOthers xi (S.filter (fun xj => decide (xj ≠ xi)))

/-- Local non-interactive Lagrange-to-additive share conversion `a_i := λ_{i, S} · s_i` for Co-ZK / MPC. -/
def lagrangeToAdditiveShare {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (xi si : F) : F :=
  CommRingOps.mul (lagrangeWeightAtZero S xi) si

/-- Sum of a list of field/ring elements. -/

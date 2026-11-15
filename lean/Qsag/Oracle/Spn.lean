module
public import Qsag.Math.Algebra
public import Qsag.Math.Gf2Pow128
public import Qsag.Spec.Bounds
public import Qsag.Spec.Encoding
public import Qsag.Oracle.Keccak
public import Qsag.Tactic.Prelude

public section

section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §2. Characteristic-2 Expansion & Differential Uniformity $\le 6$ of $S(x) = x^7$ -/

@[expose] def towerPow (k : Nat) (x : TowerElem k) : Nat → TowerElem k
  | 0 => towerOne k
  | n + 1 => towerMul k x (towerPow k x n)

/-- Algebraic $x^7$ S-box over `TowerElem k`: $S(x) = x \cdot x^2 \cdot x^4 = x^7$. -/
@[expose] def towerSbox7 (k : Nat) (x : TowerElem k) : TowerElem k :=
  let x2 := towerMul k x x
  towerMul k x (towerMul k x2 (towerMul k x2 x2))

theorem towerSbox7_eq_pow7 (k : Nat) (x : TowerElem k) :
    towerSbox7 k x = towerPow k x 7 := by
  dsimp only [towerSbox7, towerPow]
  simp only [towerMul_one, towerMul_assoc]

theorem towerSq_add (k : Nat) (a b : TowerElem k) :
    towerMul k (towerAdd k a b) (towerAdd k a b) =
      towerAdd k (towerMul k a a) (towerMul k b b) := by
  rw [towerMul_add_distrib, towerAdd_mul_distrib, towerAdd_mul_distrib,
      towerMul_comm k b a, towerAdd_assoc,
      ← towerAdd_assoc k (towerMul k a b) (towerMul k a b) (towerMul k b b),
      towerAdd_self_zero, towerZero_add]

def sbox7DiffPolyCoeffs (k : Nat) (delta outDiff : TowerElem k) : List (TowerElem k) :=
  [towerAdd k (towerPow k delta 7) outDiff, towerPow k delta 6, towerPow k delta 5,
   towerPow k delta 4, towerPow k delta 3, towerPow k delta 2, delta]

/-- **Exact Characteristic-2 Differential Polynomial Identity (`towerSbox7_diff_eq_evalCoeffs`)**:
    $(x \oplus \Delta)^7 \oplus x^7 \oplus \delta =
     (\Delta^7 \oplus \delta) \oplus \Delta^6 x \oplus \cdots \oplus \Delta x^6$. -/
theorem towerSbox7_diff_eq_evalCoeffs (k : Nat) (x delta outDiff : TowerElem k) :
    towerAdd k (towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x)) outDiff =
      RoundPoly.evalCoeffs (sbox7DiffPolyCoeffs k delta outDiff) x := by
  let x2 := towerMul k x x; let x4 := towerMul k x2 x2
  let d2 := towerMul k delta delta; let d4 := towerMul k d2 d2
  have hSboxSum :
      towerSbox7 k (towerAdd k x delta) =
        towerAdd k (towerMul k x (towerMul k x2 x4))
          (towerAdd k (towerMul k x (towerMul k x2 d4))
            (towerAdd k (towerMul k x (towerMul k d2 x4))
              (towerAdd k (towerMul k x (towerMul k d2 d4))
                (towerAdd k (towerMul k delta (towerMul k x2 x4))
                  (towerAdd k (towerMul k delta (towerMul k x2 d4))
                    (towerAdd k (towerMul k delta (towerMul k d2 x4))
                      (towerMul k delta (towerMul k d2 d4)))))))) := by
    dsimp only [towerSbox7, x4, d4]
    rw [towerSq_add k x delta]
    change towerMul k (towerAdd k x delta)
      (towerMul k (towerAdd k x2 d2) (towerMul k (towerAdd k x2 d2) (towerAdd k x2 d2))) = _
    rw [towerSq_add k x2 d2]
    simp only [towerMul_add_distrib, towerAdd_mul_distrib, towerAdd_assoc, towerAdd_left_comm]
  have hCancelX7 :
      towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x) =
        towerAdd k (towerMul k x (towerMul k x2 d4))
          (towerAdd k (towerMul k x (towerMul k d2 x4))
            (towerAdd k (towerMul k x (towerMul k d2 d4))
              (towerAdd k (towerMul k delta (towerMul k x2 x4))
                (towerAdd k (towerMul k delta (towerMul k x2 d4))
                  (towerAdd k (towerMul k delta (towerMul k d2 x4))
                    (towerMul k delta (towerMul k d2 d4))))))) := by
    rw [hSboxSum]
    change towerAdd k (towerAdd k (towerSbox7 k x) _) (towerSbox7 k x) = _
    rw [towerAdd_comm k (towerAdd k (towerSbox7 k x) _) (towerSbox7 k x), towerAdd_cancel]
  rw [hCancelX7]
  simp only [sbox7DiffPolyCoeffs, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil]
  dsimp only [CommRingOps.add, CommRingOps.mul, CommRingOps.zero, towerCommRingOps, towerPow, x2, x4, d2, d4]
  simp only [towerMul_zero, towerAdd_zero, towerMul_one, towerMul_add_distrib,
    towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k),
    towerAdd_assoc, towerAdd_comm, towerAdd_left_comm]

/-- **Exact Differential Uniformity $\le 6$ of $S(x) = x^7$ (`towerSbox7_differential_uniformity_le_six`)**:
    For every $\Delta \ne 0$, every $\delta$, and every duplicate-free `S : List (TowerElem k)`,
    at most `6` inputs $x \in S$ satisfy $S(x \oplus \Delta) \oplus S(x) = \delta$. -/
theorem towerSbox7_differential_uniformity_le_six (k : Nat)
    (delta outDiff : TowerElem k) (hDelta : delta ≠ towerZero k)
    (S : List (TowerElem k)) (hNodup : S.Nodup) :
    (S.filter (fun x =>
      decide (towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x) = outDiff))).length ≤ 6 := by
  let init : List (TowerElem k) :=
    [towerAdd k (towerPow k delta 7) outDiff, towerPow k delta 6, towerPow k delta 5,
     towerPow k delta 4, towerPow k delta 3, towerPow k delta 2]
  have hFiltEq :
      S.filter (fun x => decide (towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x) = outDiff)) =
      S.filter (fun x => decide (RoundPoly.evalCoeffs (init ++ [delta]) x = towerZero k)) := by
    congr 1; funext x
    have hId := towerSbox7_diff_eq_evalCoeffs k x delta outDiff
    have hIff : (towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x) = outDiff) ↔
        (RoundPoly.evalCoeffs (init ++ [delta]) x = towerZero k) := by
      change _ ↔ RoundPoly.evalCoeffs (sbox7DiffPolyCoeffs k delta outDiff) x = towerZero k
      rw [← hId]
      refine ⟨fun h => by rw [h, towerAdd_self_zero], fun h => ?_⟩
      have h2 := congrArg (fun z => towerAdd k z outDiff) h
      simpa only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] using h2
    by_cases hp : towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x) = outDiff
    · have hq : RoundPoly.evalCoeffs (init ++ [delta]) x = towerZero k := hIff.mp hp
      simp [hp, hq]
    · have hq : ¬ (RoundPoly.evalCoeffs (init ++ [delta]) x = towerZero k) := fun h => hp (hIff.mpr h)
      simp [hp, hq]
  rw [hFiltEq]
  exact evalCoeffs_roots_le_of_lead_nonzero 6 init delta S rfl hDelta hNodup

@[expose] def sbox7MaxDiffProb128 : RatBound := ⟨6, 2 ^ 128, Nat.two_pow_pos 128⟩
def sbox7MaxDiffProb128Reduced : RatBound := ⟨3, 2 ^ 127, Nat.two_pow_pos 127⟩

theorem sbox7MaxDiffProb128_eq_three_div_two_pow_127 :
    RatBound.le sbox7MaxDiffProb128 sbox7MaxDiffProb128Reduced ∧
    RatBound.le sbox7MaxDiffProb128Reduced sbox7MaxDiffProb128 ∧
    strictlyMoreThanBits 125 sbox7MaxDiffProb128 :=
  ⟨by decide, by decide, by decide⟩

/-! ## §3. Wiedemann Tower Frobenius Periodicity & Two-Sided Bijectivity of $x \mapsto x^7$ on $\mathcal{T}_7$ -/

def towerFrobIter (k : Nat) : Nat → TowerElem k → TowerElem k
  | 0, a => a
  | m + 1, a => let prev := towerFrobIter k m a; towerMul k prev prev

theorem towerFrobIter_add (k : Nat) :
    ∀ (m : Nat) (a b : TowerElem k),
      towerFrobIter k m (towerAdd k a b) = towerAdd k (towerFrobIter k m a) (towerFrobIter k m b)
  | 0, _, _ => rfl
  | m + 1, a, b => by simp only [towerFrobIter, towerFrobIter_add k m a b]; exact towerSq_add k _ _

theorem towerFrobIter_mul (k : Nat) :
    ∀ (m : Nat) (a b : TowerElem k),
      towerFrobIter k m (towerMul k a b) = towerMul k (towerFrobIter k m a) (towerFrobIter k m b)
  | 0, _, _ => rfl
  | m + 1, a, b => by
    simp only [towerFrobIter, towerFrobIter_mul k m a b,
      towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]

theorem towerFrobIter_add_steps (k : Nat) :
    ∀ (m n : Nat) (a : TowerElem k),
      towerFrobIter k (m + n) a = towerFrobIter k m (towerFrobIter k n a)
  | 0, n, a => by simp [Nat.zero_add, towerFrobIter]
  | m + 1, n, a => by
    rw [Nat.succ_add m n]; simp only [towerFrobIter, towerFrobIter_add_steps k m n a]

theorem towerFrobIter_embed (k : Nat) :
    ∀ (m : Nat) (a : TowerElem k),
      towerFrobIter (k + 1) m (embedTower k a) = embedTower k (towerFrobIter k m a)
  | 0, _ => rfl
  | m + 1, a => by simp only [towerFrobIter, towerFrobIter_embed k m a, embedTower_mul]

private def artinSchreierZ (k : Nat) : TowerElem (k + 1) := (towerZero k, towerInvX k)

private theorem artinSchreierZ_sq (k : Nat) :
    towerMul (k + 1) (artinSchreierZ k) (artinSchreierZ k) =
      towerAdd (k + 1) (embedTower k (towerMul k (towerInvX k) (towerInvX k))) (artinSchreierZ k) := by
  simp only [artinSchreierZ, embedTower, towerMul, towerAdd,
    towerMul_zero, towerZero_mul, towerZero_add, towerAdd_zero]
  congr 1
  rw [← towerMul_assoc, towerX_mul_invX, towerOne_mul]

private theorem towerFrobIter_artinSchreierZ (k : Nat) :
    ∀ m : Nat, ∃ c : TowerElem k,
      towerFrobIter (k + 1) m (artinSchreierZ k) = towerAdd (k + 1) (embedTower k c) (artinSchreierZ k)
  | 0 => ⟨towerZero k, by simp [towerFrobIter, embedTower_zero]⟩
  | m + 1 => by
    obtain ⟨c, hc⟩ := towerFrobIter_artinSchreierZ k m
    refine ⟨towerAdd k (towerMul k c c) (towerMul k (towerInvX k) (towerInvX k)), ?_⟩
    simp only [towerFrobIter]
    rw [hc, towerSq_add (k + 1), ← embedTower_mul, artinSchreierZ_sq, ← towerAdd_assoc, ← embedTower_add]

/-- **Fermat's Little Theorem on the Wiedemann Binary Tower (`towerFrobIter_card_eq`)**:
    $a^{2^{2^k}} = a$ for every tower level $k$ and $a \in \mathcal{T}_k$. -/
theorem towerFrobIter_card_eq :
    ∀ (k : Nat) (a : TowerElem k), towerFrobIter k (2 ^ k) a = a
  | 0, a => by cases a <;> rfl
  | k + 1, a => by
    have hDecomp : a = towerAdd (k + 1) (embedTower k a.1)
        (towerMul (k + 1) (embedTower k (towerMul k a.2 (towerX k))) (artinSchreierZ k)) := by
      rcases a with ⟨a1, a2⟩
      simp only [embedTower, artinSchreierZ, towerMul, towerAdd,
        towerMul_zero, towerZero_mul, towerAdd_zero, towerZero_add]
      congr 1
      rw [towerMul_assoc, towerX_mul_invX, towerMul_one]
    have hPow2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
    have hZ : towerFrobIter (k + 1) (2 ^ (k + 1)) (artinSchreierZ k) = artinSchreierZ k := by
      obtain ⟨c, hc⟩ := towerFrobIter_artinSchreierZ k (2 ^ k)
      rw [hPow2, towerFrobIter_add_steps (k + 1) (2 ^ k) (2 ^ k), hc, towerFrobIter_add,
          towerFrobIter_embed, towerFrobIter_card_eq k c, hc, ← towerAdd_assoc,
          towerAdd_self_zero, towerZero_add]
    calc towerFrobIter (k + 1) (2 ^ (k + 1)) a
      _ = towerFrobIter (k + 1) (2 ^ (k + 1))
            (towerAdd (k + 1) (embedTower k a.1)
              (towerMul (k + 1) (embedTower k (towerMul k a.2 (towerX k))) (artinSchreierZ k))) := by
            rw [← hDecomp]
      _ = towerAdd (k + 1) (embedTower k (towerFrobIter k (2 ^ (k + 1)) a.1))
            (towerMul (k + 1) (embedTower k (towerFrobIter k (2 ^ (k + 1)) (towerMul k a.2 (towerX k))))
              (artinSchreierZ k)) := by
            rw [towerFrobIter_add, towerFrobIter_mul, towerFrobIter_embed, towerFrobIter_embed, hZ]
      _ = a := by
            rw [hPow2, towerFrobIter_add_steps k (2 ^ k) (2 ^ k), towerFrobIter_card_eq k,
                towerFrobIter_card_eq k, towerFrobIter_add_steps k (2 ^ k) (2 ^ k),
                towerFrobIter_card_eq k, towerFrobIter_card_eq k]
            exact hDecomp.symm

def octGeom128 : Nat → Tower128 → Tower128
  | 0, _ => towerOne 7
  | m + 1, z => towerMul 7 z (towerFrobIter 7 3 (octGeom128 m z))

/-- Explicit constructive inverse $S^{-1}(z) = z^{(8^{43} - 1) / 7}$ of $S(x) = x^7$ on `Tower128`. -/
def towerSbox7Inv128 (z : Tower128) : Tower128 := octGeom128 43 z

private theorem frobIter3_eq_pow8 (y : Tower128) :
    towerFrobIter 7 3 y = towerMul 7 (towerSbox7 7 y) y := by
  dsimp only [towerFrobIter, towerSbox7]
  simp only [towerMul_assoc]

private theorem octGeom128_sbox7_mul :
    ∀ (m : Nat) (y : Tower128),
      towerMul 7 (octGeom128 m (towerSbox7 7 y)) y = towerFrobIter 7 (3 * m) y
  | 0, y => by simp [octGeom128, towerFrobIter]
  | m + 1, y => by
    simp only [octGeom128]
    have hRearr :
        towerMul 7 (towerMul 7 (towerSbox7 7 y) (towerFrobIter 7 3 (octGeom128 m (towerSbox7 7 y)))) y =
        towerMul 7 (towerMul 7 (towerSbox7 7 y) y) (towerFrobIter 7 3 (octGeom128 m (towerSbox7 7 y))) := by
      simp only [towerMul_comm, towerMul_left_comm_of_assoc 7 (towerMul_assoc 7)]
    rw [hRearr, ← frobIter3_eq_pow8 y, ← towerFrobIter_mul 7 3 y,
        towerMul_comm 7 y (octGeom128 m (towerSbox7 7 y)), octGeom128_sbox7_mul m y,
        ← towerFrobIter_add_steps 7 3 (3 * m) y, show 3 + 3 * m = 3 * (m + 1) by omega]

theorem towerSbox7Inv128_left_inv (x : Tower128) :
    towerSbox7Inv128 (towerSbox7 7 x) = x := by
  by_cases hx : x = towerZero 7
  · subst hx; simp [towerSbox7, towerSbox7Inv128, octGeom128]
  · apply towerMul_cancel_left 7 x _ _ hx
    rw [towerMul_comm 7 x, towerSbox7Inv128, octGeom128_sbox7_mul 43 x,
        show (3 : Nat) * 43 = 1 + 2 ^ 7 by decide,
        towerFrobIter_add_steps 7 1 (2 ^ 7) x, towerFrobIter_card_eq 7 x]
    rfl

private theorem octGeom128_comm_sbox7 :
    ∀ (m : Nat) (z : Tower128), towerSbox7 7 (octGeom128 m z) = octGeom128 m (towerSbox7 7 z)
  | 0, _ => by simp [octGeom128, towerSbox7]
  | m + 1, z => by
    have hMul : ∀ a b : Tower128, towerSbox7 7 (towerMul 7 a b) =
        towerMul 7 (towerSbox7 7 a) (towerSbox7 7 b) := fun a b => by
      dsimp only [towerSbox7]
      simp only [towerMul_comm, towerMul_left_comm_of_assoc 7 (towerMul_assoc 7)]
    have hFrob : ∀ a : Tower128, towerSbox7 7 (towerFrobIter 7 3 a) =
        towerFrobIter 7 3 (towerSbox7 7 a) := fun a => by
      dsimp only [towerSbox7]; simp only [towerFrobIter_mul]
    simp only [octGeom128, hMul, hFrob, octGeom128_comm_sbox7 m z]

theorem towerSbox7Inv128_right_inv (z : Tower128) :
    towerSbox7 7 (towerSbox7Inv128 z) = z := by
  unfold towerSbox7Inv128; rw [octGeom128_comm_sbox7 43 z]; exact towerSbox7Inv128_left_inv z

/-- **Full Bijectivity of $S(x) = x^7$ on `Tower128` (`pow7_tower128_bijective`)**. -/
theorem pow7_tower128_bijective : IsBijective (towerSbox7 7) :=
  ⟨fun a b h => by
      have := congrArg towerSbox7Inv128 h
      rwa [towerSbox7Inv128_left_inv, towerSbox7Inv128_left_inv] at this,
   fun z => ⟨towerSbox7Inv128 z, towerSbox7Inv128_right_inv z⟩⟩

theorem towerSbox7_diff_zero_iff (x delta : Tower128) :
    towerAdd 7 (towerSbox7 7 (towerAdd 7 x delta)) (towerSbox7 7 x) = towerZero 7 ↔
      delta = towerZero 7 := by
  refine ⟨fun h => ?_, fun h => by subst h; simp [towerAdd_zero, towerAdd_self_zero]⟩
  have hEq : towerSbox7 7 (towerAdd 7 x delta) = towerSbox7 7 x := by
    have h2 := congrArg (fun u => towerAdd 7 u (towerSbox7 7 x)) h
    simpa only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] using h2
  have h3 := congrArg (towerAdd 7 x) (pow7_tower128_bijective.1 _ _ hEq)
  simpa only [towerAdd_cancel, towerAdd_self_zero] using h3

/-! ## §4. Concrete MDS Linear Layer Branch Number $= 3$ & 48-Round Active S-Box Counts -/

@[expose] def spnRounds : Nat := 48
def gf128MdsAPolyBits : BitVec 128 := 0x9E3779B97F4A7C15F39CC0605CEDC835#128
def gf128MdsBPolyBits : BitVec 128 := 0xBF58476D1CE4E5B994D049BB133111EB#128
def gf128MdsATowerBits : BitVec 128 := 0x6938822d2669c41b597c42deeb84a0bb#128
def gf128MdsBTowerBits : BitVec 128 := 0x2df5aeeede6d3f143c5406b243efb482#128
def gf128MdsATower : Tower128 := unpackTower 7 gf128MdsATowerBits
def gf128MdsBTower : Tower128 := unpackTower 7 gf128MdsBTowerBits


theorem towerOne128_ne_zero : towerOne 7 ≠ towerZero 7 := towerOne_ne_zero 7

theorem gf128_mds_constants_certified :
    psiTower128ToPoly gf128MdsATower = gf128MdsAPolyBits ∧
    psiTower128ToPoly gf128MdsBTower = gf128MdsBPolyBits ∧
    gf128MdsATower ≠ towerZero 7 ∧ gf128MdsBTower ≠ towerZero 7 ∧
    towerMul 7 gf128MdsATower gf128MdsBTower ≠ towerOne 7 ∧
    gf2_128_mul_bv gf128MdsAPolyBits gf128MdsBPolyBits ≠ 1#128 := by
  obtain ⟨ha, hb, hm⟩ := gf128_linear_layer_basis_certificate
  change psiTower128ToPoly gf128MdsATower = gf128MdsAPolyBits at ha
  change psiTower128ToPoly gf128MdsBTower = gf128MdsBPolyBits at hb
  change gf2_128_mul_bv gf128MdsAPolyBits gf128MdsBPolyBits ≠ 1#128 at hm
  refine ⟨ha, hb, ?_, ?_, ?_, hm⟩
  · intro h
    rw [h, psiTower128ToPoly_zero] at ha
    exact (by decide : (0#128 : BitVec 128) ≠ gf128MdsAPolyBits) ha
  · intro h
    rw [h, psiTower128ToPoly_zero] at hb
    exact (by decide : (0#128 : BitVec 128) ≠ gf128MdsBPolyBits) hb
  · intro h
    have hp := congrArg psiTower128ToPoly h
    rw [psiTower128ToPoly_mul, ha, hb, psiTower128ToPoly_one] at hp
    exact hm hp

structure ValidSpnMdsPair (k : Nat) where
  mdsA : TowerElem k
  mdsB : TowerElem k
  hA_ne_zero : mdsA ≠ towerZero k
  hB_ne_zero : mdsB ≠ towerZero k
  hAB_ne_one : towerMul k mdsA mdsB ≠ towerOne k

def parallelSeededMdsPair : ValidSpnMdsPair 7 where
  mdsA := gf128MdsATower
  mdsB := gf128MdsBTower
  hA_ne_zero := gf128_mds_constants_certified.2.2.1
  hB_ne_zero := gf128_mds_constants_certified.2.2.2.1
  hAB_ne_one := gf128_mds_constants_certified.2.2.2.2.1

@[expose] def spnLinearMix (k : Nat) (mdsA mdsB : TowerElem k)
    (st : TowerElem k × TowerElem k) : TowerElem k × TowerElem k :=
  (towerAdd k st.1 (towerMul k mdsA st.2), towerAdd k st.2 (towerMul k mdsB st.1))

@[expose] def laneActiveWeight (k : Nat) (st : TowerElem k × TowerElem k) : Nat :=
  (if st.1 = towerZero k then 0 else 1) + (if st.2 = towerZero k then 0 else 1)

theorem laneActiveWeight_eq_zero_iff (k : Nat) (st : TowerElem k × TowerElem k) :
    laneActiveWeight k st = 0 ↔ st = (towerZero k, towerZero k) := by
  unfold laneActiveWeight; rcases st with ⟨u, v⟩
  by_cases hu : u = towerZero k <;> by_cases hv : v = towerZero k <;> simp [hu, hv]

/-- **Exact Differential Branch Number $= 3$ of `spnLinearMix` (`spnLinearMix_branch_number_three`)**. -/
theorem spnLinearMix_branch_number_three {k : Nat} (mds : ValidSpnMdsPair k)
    (st : TowerElem k × TowerElem k) (hNonZero : st ≠ (towerZero k, towerZero k)) :
    spnLinearMix k mds.mdsA mds.mdsB st ≠ (towerZero k, towerZero k) ∧
    3 ≤ laneActiveWeight k st + laneActiveWeight k (spnLinearMix k mds.mdsA mds.mdsB st) := by
  rcases st with ⟨u, v⟩
  have hOutNeZero : spnLinearMix k mds.mdsA mds.mdsB (u, v) ≠ (towerZero k, towerZero k) := by
    intro hZero
    dsimp only [spnLinearMix] at hZero
    have huEq : u = towerMul k mds.mdsA v := by
      have h := congrArg (fun z => towerAdd k z (towerMul k mds.mdsA v)) (congrArg Prod.fst hZero)
      simpa only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] using h
    have hvEq : v = towerMul k mds.mdsB u := by
      have h := congrArg (fun z => towerAdd k z (towerMul k mds.mdsB u)) (congrArg Prod.snd hZero)
      simpa only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] using h
    by_cases hv0 : v = towerZero k
    · subst hv0; simp only [towerMul_zero] at huEq; exact hNonZero (Prod.ext huEq rfl)
    · have hvLoop : towerMul k (towerOne k) v = towerMul k (towerMul k mds.mdsB mds.mdsA) v :=
        calc towerMul k (towerOne k) v
          _ = v := towerOne_mul k v
          _ = towerMul k mds.mdsB u := hvEq
          _ = towerMul k mds.mdsB (towerMul k mds.mdsA v) := by rw [huEq]
          _ = towerMul k (towerMul k mds.mdsB mds.mdsA) v := (towerMul_assoc k _ _ _).symm
      have hOneEqBA : towerOne k = towerMul k mds.mdsB mds.mdsA :=
        towerMul_cancel_left k v (towerOne k) (towerMul k mds.mdsB mds.mdsA) hv0
          (by rw [towerMul_comm k v, towerMul_comm k v, hvLoop])
      rw [towerMul_comm] at hOneEqBA
      exact mds.hAB_ne_one hOneEqBA.symm
  refine ⟨hOutNeZero, ?_⟩
  by_cases hu : u = towerZero k
  · have hv : v ≠ towerZero k := fun hv0 => hNonZero (Prod.ext hu hv0)
    have hAv : towerMul k mds.mdsA v ≠ towerZero k := fun hMul0 =>
      ((towerMul_eq_zero_iff k mds.mdsA v).mp hMul0).elim mds.hA_ne_zero hv
    unfold laneActiveWeight spnLinearMix; simp [hu, hv, hAv]
  · by_cases hv : v = towerZero k
    · have hBu : towerMul k mds.mdsB u ≠ towerZero k := fun hMul0 =>
        ((towerMul_eq_zero_iff k mds.mdsB u).mp hMul0).elim mds.hB_ne_zero hu
      unfold laneActiveWeight spnLinearMix; simp [hu, hv, hBu]
    · have hOutWtPos : 0 < laneActiveWeight k (spnLinearMix k mds.mdsA mds.mdsB (u, v)) := by
        cases hWt : laneActiveWeight k (spnLinearMix k mds.mdsA mds.mdsB (u, v)) with
        | zero => exact False.elim (hOutNeZero ((laneActiveWeight_eq_zero_iff k _).mp hWt))
        | succ m => exact Nat.zero_lt_succ m
      have hInWt : laneActiveWeight k (u, v) = 2 := by unfold laneActiveWeight; simp [hu, hv]
      omega

@[expose] def spnRound128 (mdsA mdsB : Tower128) (rc : Tower128 × Tower128)
    (st : Tower128 × Tower128) : Tower128 × Tower128 :=
  spnLinearMix 7 mdsA mdsB (towerSbox7 7 (towerAdd 7 st.1 rc.1), towerSbox7 7 (towerAdd 7 st.2 rc.2))

def spnIterRounds128 (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128) :
    Nat → (Tower128 × Tower128) → Tower128 × Tower128
  | 0, st => st
  | r + 1, st => spnRound128 mdsA mdsB (rcs r) (spnIterRounds128 mdsA mdsB rcs r st)

def spnDaviesMeyer48 (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128)
    (inp : Tower128 × Tower128) : Tower128 × Tower128 :=
  let out := spnIterRounds128 mdsA mdsB rcs spnRounds inp
  (towerAdd 7 out.1 inp.1, towerAdd 7 out.2 inp.2)

def spnTrailActiveSboxes (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128) :
    Nat → (Tower128 × Tower128) → (Tower128 × Tower128) → Nat
  | 0, _, _ => 0
  | r + 1, s, s' =>
    let cur := spnIterRounds128 mdsA mdsB rcs r s
    let cur' := spnIterRounds128 mdsA mdsB rcs r s'
    spnTrailActiveSboxes mdsA mdsB rcs r s s' +
      laneActiveWeight 7 (towerAdd 7 cur.1 cur'.1, towerAdd 7 cur.2 cur'.2)

private theorem spnLinearMix_diff (mdsA mdsB : Tower128) (a b : Tower128 × Tower128) :
    let la := spnLinearMix 7 mdsA mdsB a; let lb := spnLinearMix 7 mdsA mdsB b
    (towerAdd 7 la.1 lb.1, towerAdd 7 la.2 lb.2) =
      spnLinearMix 7 mdsA mdsB (towerAdd 7 a.1 b.1, towerAdd 7 a.2 b.2) := by
  unfold spnLinearMix
  apply Prod.ext <;> simp only [towerMul_add_distrib, towerAdd_assoc, towerAdd_left_comm]

private theorem sboxPair_diff_weight_eq (rc a b : Tower128 × Tower128) :
    laneActiveWeight 7
      (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.1 rc.1)) (towerSbox7 7 (towerAdd 7 b.1 rc.1)),
       towerAdd 7 (towerSbox7 7 (towerAdd 7 a.2 rc.2)) (towerSbox7 7 (towerAdd 7 b.2 rc.2))) =
    laneActiveWeight 7 (towerAdd 7 a.1 b.1, towerAdd 7 a.2 b.2) := by
  have hShift : ∀ x y r : Tower128,
      towerAdd 7 y r = towerAdd 7 (towerAdd 7 x r) (towerAdd 7 x y) := fun x y r => by
    rw [towerAdd_comm 7 x r, towerAdd_assoc 7 r x, ← towerAdd_assoc 7 x x y,
        towerAdd_self_zero, towerZero_add, towerAdd_comm 7 r y]
  have h0 : (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.1 rc.1)) (towerSbox7 7 (towerAdd 7 b.1 rc.1)) = towerZero 7) ↔
      (towerAdd 7 a.1 b.1 = towerZero 7) := by
    rw [hShift a.1 b.1 rc.1, towerAdd_comm 7 (towerSbox7 7 (towerAdd 7 a.1 rc.1)), towerSbox7_diff_zero_iff]
  have h1 : (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.2 rc.2)) (towerSbox7 7 (towerAdd 7 b.2 rc.2)) = towerZero 7) ↔
      (towerAdd 7 a.2 b.2 = towerZero 7) := by
    rw [hShift a.2 b.2 rc.2, towerAdd_comm 7 (towerSbox7 7 (towerAdd 7 a.2 rc.2)), towerSbox7_diff_zero_iff]
  unfold laneActiveWeight
  by_cases d0 : towerAdd 7 a.1 b.1 = towerZero 7 <;> by_cases d1 : towerAdd 7 a.2 b.2 = towerZero 7
  · simp [d0, d1, h0.mpr d0, h1.mpr d1]
  · have nd1 : ¬ (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.2 rc.2)) (towerSbox7 7 (towerAdd 7 b.2 rc.2)) = towerZero 7) :=
      fun h => d1 (h1.mp h)
    simp [d0, d1, h0.mpr d0, nd1]
  · have nd0 : ¬ (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.1 rc.1)) (towerSbox7 7 (towerAdd 7 b.1 rc.1)) = towerZero 7) :=
      fun h => d0 (h0.mp h)
    simp [d0, d1, nd0, h1.mpr d1]
  · have nd0 : ¬ (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.1 rc.1)) (towerSbox7 7 (towerAdd 7 b.1 rc.1)) = towerZero 7) :=
      fun h => d0 (h0.mp h)
    have nd1 : ¬ (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.2 rc.2)) (towerSbox7 7 (towerAdd 7 b.2 rc.2)) = towerZero 7) :=
      fun h => d1 (h1.mp h)
    simp [d0, d1, nd0, nd1]

private theorem spnRound128_preserves_distinct (mds : ValidSpnMdsPair 7)
    (rc s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    spnRound128 mds.mdsA mds.mdsB rc s ≠ spnRound128 mds.mdsA mds.mdsB rc s' ∧
    3 ≤ laneActiveWeight 7 (towerAdd 7 s.1 s'.1, towerAdd 7 s.2 s'.2) +
        laneActiveWeight 7
          (towerAdd 7 (spnRound128 mds.mdsA mds.mdsB rc s).1 (spnRound128 mds.mdsA mds.mdsB rc s').1,
           towerAdd 7 (spnRound128 mds.mdsA mds.mdsB rc s).2 (spnRound128 mds.mdsA mds.mdsB rc s').2) := by
  let sbS := (towerSbox7 7 (towerAdd 7 s.1 rc.1), towerSbox7 7 (towerAdd 7 s.2 rc.2))
  let sbS' := (towerSbox7 7 (towerAdd 7 s'.1 rc.1), towerSbox7 7 (towerAdd 7 s'.2 rc.2))
  have hDiffInNe : (towerAdd 7 s.1 s'.1, towerAdd 7 s.2 s'.2) ≠ (towerZero 7, towerZero 7) := by
    intro h0
    have h1 := congrArg (fun z => towerAdd 7 z s'.1) (congrArg Prod.fst h0)
    have h2 := congrArg (fun z => towerAdd 7 z s'.2) (congrArg Prod.snd h0)
    simp only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] at h1 h2
    exact hNe (Prod.ext h1 h2)
  have hSbWt := sboxPair_diff_weight_eq rc s s'
  have hSbDiffNe : (towerAdd 7 sbS.1 sbS'.1, towerAdd 7 sbS.2 sbS'.2) ≠ (towerZero 7, towerZero 7) := by
    intro h0
    have hw0 := (laneActiveWeight_eq_zero_iff 7 _).mpr h0
    rw [hSbWt] at hw0
    exact hDiffInNe ((laneActiveWeight_eq_zero_iff 7 _).mp hw0)
  have hBranch := spnLinearMix_branch_number_three mds _ hSbDiffNe
  have hMixEq := spnLinearMix_diff mds.mdsA mds.mdsB sbS sbS'
  unfold spnRound128; dsimp only [sbS, sbS'] at hMixEq ⊢
  refine ⟨fun hEqOut => hBranch.1 (by rw [← hMixEq, hEqOut, towerAdd_self_zero, towerAdd_self_zero]), ?_⟩
  rw [hMixEq, ← hSbWt]; exact hBranch.2

private theorem spnIterRounds_even_active_bound (mds : ValidSpnMdsPair 7)
    (rcs : Nat → Tower128 × Tower128) :
    ∀ (pairs : Nat) (s s' : Tower128 × Tower128), s ≠ s' →
      spnIterRounds128 mds.mdsA mds.mdsB rcs (2 * pairs) s ≠
        spnIterRounds128 mds.mdsA mds.mdsB rcs (2 * pairs) s' ∧
      3 * pairs ≤ spnTrailActiveSboxes mds.mdsA mds.mdsB rcs (2 * pairs) s s'
  | 0, _, _, hNe => ⟨hNe, Nat.le_refl 0⟩
  | pairs + 1, s, s', hNe => by
    obtain ⟨hNePrev, hActPrev⟩ := spnIterRounds_even_active_bound mds rcs pairs s s' hNe
    rw [show 2 * (pairs + 1) = (2 * pairs + 1) + 1 by omega]
    let u := spnIterRounds128 mds.mdsA mds.mdsB rcs (2 * pairs) s
    let u' := spnIterRounds128 mds.mdsA mds.mdsB rcs (2 * pairs) s'
    obtain ⟨hNeMid, hStep3⟩ := spnRound128_preserves_distinct mds (rcs (2 * pairs)) u u' hNePrev
    obtain ⟨hNeEnd, _⟩ := spnRound128_preserves_distinct mds (rcs (2 * pairs + 1))
      (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u)
      (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u') hNeMid
    refine ⟨hNeEnd, ?_⟩
    simp only [spnTrailActiveSboxes, spnIterRounds128]
    change 3 * (pairs + 1) ≤ spnTrailActiveSboxes mds.mdsA mds.mdsB rcs (2 * pairs) s s' +
      laneActiveWeight 7 (towerAdd 7 u.1 u'.1, towerAdd 7 u.2 u'.2) +
      laneActiveWeight 7
        (towerAdd 7 (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u).1
                    (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u').1,
         towerAdd 7 (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u).2
                    (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u').2)
    omega

/-- **48-Round Active S-Box Lower Bound (`spn48_active_sboxes_ge_72`)**:
    Every distinct 256-bit input pair `s ≠ s'` activates **$\ge 72$ S-boxes** ($\ge 48$). -/
theorem spn48_active_sboxes_ge_72 (mds : ValidSpnMdsPair 7)
    (rcs : Nat → Tower128 × Tower128) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    72 ≤ spnTrailActiveSboxes mds.mdsA mds.mdsB rcs spnRounds s s' ∧
    48 ≤ spnTrailActiveSboxes mds.mdsA mds.mdsB rcs spnRounds s s' := by
  have h := (spnIterRounds_even_active_bound mds rcs 24 s s' hNe).2
  exact ⟨h, Nat.le_trans (by decide : 48 ≤ 72) h⟩

/-- Arithmetic powers of the one-S-box root fraction. No independence or conditional
    uniformity follows from an active-box count. In particular, a nonempty trail event under
    a fixed public 256-bit permutation has probability at least `2^-256`; these smaller
    products cannot bound all such events. See `HashTrailSampling` for an explicit fresh-input
    product experiment and the deterministic-trace obstruction. Historical theorem name retained. -/
theorem spn48_differential_trail_security_bounds :
    strictlyMoreThanBits 376 (sbox7MaxDiffProb128.pow 3) ∧
    strictlyMoreThanBits 256 (sbox7MaxDiffProb128.pow 48) ∧
    strictlyMoreThanBits 256 (sbox7MaxDiffProb128.pow 72) := by
  have h1 : RatBound.le sbox7MaxDiffProb128 (RatBound.invPow2 125) :=
    (atLeastBits_iff_le_invPow2 125 sbox7MaxDiffProb128).mp
      (atLeastBits_of_strictlyMoreThanBits sbox7MaxDiffProb128_eq_three_div_two_pow_127.2.2)
  have hBits : ∀ n : Nat, atLeastBits (125 * n) (sbox7MaxDiffProb128.pow n) := fun n => by
    apply atLeastBits_of_le (RatBound.pow_le_pow h1 n)
    unfold atLeastBits RatBound.invPow2 RatBound.pow; dsimp only
    rw [Nat.one_pow, Nat.one_mul, ← Nat.pow_mul]; exact Nat.le_refl _
  have hStrictFrom257 : ∀ r : RatBound, atLeastBits 257 r → strictlyMoreThanBits 256 r := by
    intro r hr; unfold atLeastBits strictlyMoreThanBits at *
    by_cases hNum : r.num = 0
    · rw [hNum, Nat.zero_mul]; exact r.h_pos
    · exact Nat.lt_of_lt_of_le (by rw [Nat.pow_succ, ← Nat.mul_assoc]; omega) hr
  exact ⟨by decide,
    hStrictFrom257 _ (atLeastBits_antitone_bits (by decide : 257 ≤ 125 * 48) (hBits 48)),
    hStrictFrom257 _ (atLeastBits_antitone_bits (by decide : 257 ≤ 125 * 72) (hBits 72))⟩

/-! ## §5. Nominal Degree Schedule Arithmetic & `#tooth` Guards -/

private def binaryPopcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n + 1 => ((n + 1) % 2) + binaryPopcountAux fuel ((n + 1) / 2)

def binaryPopcount (n : Nat) : Nat := binaryPopcountAux n n

/-- A nominal schedule, not the degree of an interpreted SPN polynomial. -/
@[expose] def spnMultivariateDegreeSchedule (r : Nat) : Nat := Nat.min 127 (3 ^ r)
def spnUnivariateDegree (r : Nat) : Nat := 7 ^ r

/-- Nominal schedule and exponent arithmetic. No actual-degree or security-margin theorem
    follows without proving noncancellation and a connection to an attack model. -/
theorem spn48_algebraic_degree_margin :
    binaryPopcount 7 = 3 ∧ 3 ^ 5 = 243 ∧ 128 < 3 ^ 5 ∧
    spnMultivariateDegreeSchedule 5 = 127 ∧ spnRounds - 5 = 43 ∧
    2 ^ 134 < spnUnivariateDegree spnRounds :=
  ⟨by decide, by decide, by decide, by decide, rfl, by decide⟩

/-- **Round-Constant Asymmetry Eliminates Zero-Subspace Fixpoints (`spnRound128_nonzero_rc_breaks_zero_fixpoint`)**. -/
theorem spnRound128_nonzero_rc_breaks_zero_fixpoint
    (mds : ValidSpnMdsPair 7) (rc : Tower128 × Tower128) (hRc : rc ≠ (towerZero 7, towerZero 7)) :
    spnRound128 mds.mdsA mds.mdsB rc (towerZero 7, towerZero 7) ≠ (towerZero 7, towerZero 7) := by
  have hSboxNe : (towerSbox7 7 rc.1, towerSbox7 7 rc.2) ≠ (towerZero 7, towerZero 7) := by
    intro h0
    have h1 : rc.1 = towerZero 7 := pow7_tower128_bijective.1 _ _ (by simpa [towerSbox7] using congrArg Prod.fst h0)
    have h2 : rc.2 = towerZero 7 := pow7_tower128_bijective.1 _ _ (by simpa [towerSbox7] using congrArg Prod.snd h0)
    exact hRc (Prod.ext h1 h2)
  unfold spnRound128; simp only [towerZero_add]
  exact (spnLinearMix_branch_number_three mds (towerSbox7 7 rc.1, towerSbox7 7 rc.2) hSboxNe).1


end Qsag
end


section
namespace Qsag
open MigrationExecution

set_option autoImplicit false

/-! ## 1. Rust arithmetic model -/

/-- `pow7_plain` (`parallel_mpc.rs:510`): `x2 = x·x`, `x4 = x2·x2`, `(x·x2)·x4`. -/
def rustPow7 (x : BitVec 128) : BitVec 128 :=
  let x2 := rustGf128Mul x x
  let x4 := rustGf128Mul x2 x2
  rustGf128Mul (rustGf128Mul x x2) x4

/-- One iteration of the loop in `algebraic_step_plain` (`parallel_mpc.rs:529-538`). -/
def rustSpnRound (rc st : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  let x7 := rustPow7 (st.1 ^^^ rc.1)
  let y7 := rustPow7 (st.2 ^^^ rc.2)
  (x7 ^^^ rustGf128Mul y7 gf128MdsAPolyBits, y7 ^^^ rustGf128Mul x7 gf128MdsBPolyBits)

/-- The first `r` loop iterations; `rcs round` is `round_constants(c0, c1, round)`. -/
def rustSpnIter (rcs : Nat → BitVec 128 × BitVec 128) :
    Nat → BitVec 128 × BitVec 128 → BitVec 128 × BitVec 128
  | 0, st => st
  | r + 1, st => rustSpnRound (rcs r) (rustSpnIter rcs r st)

/-- `algebraic_step_plain`: 48 rounds, then `(state.0 ^ input.0, state.1 ^ input.1)`. -/
def rustAlgebraicStep (rcs : Nat → BitVec 128 × BitVec 128)
    (inp : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  let out := rustSpnIter rcs spnRounds inp
  (out.1 ^^^ inp.1, out.2 ^^^ inp.2)

/-! ## 2. Lane-pair basis change -/

def psiTower128Pair (p : Tower128 × Tower128) : BitVec 128 × BitVec 128 :=
  (psiTower128ToPoly p.1, psiTower128ToPoly p.2)

def polyToTower128Pair (p : BitVec 128 × BitVec 128) : Tower128 × Tower128 :=
  (polyToTower128 p.1, polyToTower128 p.2)

theorem psiTower128Pair_polyToTower128Pair (p : BitVec 128 × BitVec 128) :
    psiTower128Pair (polyToTower128Pair p) = p :=
  Prod.ext (psiTower128ToPoly_polyToTower128 p.1) (psiTower128ToPoly_polyToTower128 p.2)

theorem polyToTower128Pair_psiTower128Pair (p : Tower128 × Tower128) :
    polyToTower128Pair (psiTower128Pair p) = p :=
  Prod.ext (polyToTower128_psiTower128ToPoly p.1) (polyToTower128_psiTower128ToPoly p.2)

theorem psiTower128Pair_injective (p q : Tower128 × Tower128)
    (h : psiTower128Pair p = psiTower128Pair q) : p = q := by
  have hc := congrArg polyToTower128Pair h
  rw [polyToTower128Pair_psiTower128Pair, polyToTower128Pair_psiTower128Pair] at hc
  exact hc

theorem polyToTower128Pair_injective (p q : BitVec 128 × BitVec 128)
    (h : polyToTower128Pair p = polyToTower128Pair q) : p = q := by
  have hc := congrArg psiTower128Pair h
  rw [psiTower128Pair_polyToTower128Pair, psiTower128Pair_polyToTower128Pair] at hc
  exact hc

/-! ## 3. Transport of the S-box, the mixing layer, the rounds and Davies–Meyer -/

theorem psiTower128ToPoly_sbox7 (x : Tower128) :
    psiTower128ToPoly (towerSbox7 7 x) = rustPow7 (psiTower128ToPoly x) := by
  unfold towerSbox7 rustPow7
  simp only [psiTower128ToPoly_mul_rust, rustGf128Mul_assoc]

theorem polyToTower128_rustPow7 (a : BitVec 128) :
    polyToTower128 (rustPow7 a) = towerSbox7 7 (polyToTower128 a) := by
  apply psiTower128ToPoly_injective
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_sbox7,
    psiTower128ToPoly_polyToTower128]

theorem psiTower128Pair_spnLinearMix (st : Tower128 × Tower128) :
    psiTower128Pair (spnLinearMix 7 gf128MdsATower gf128MdsBTower st) =
      (psiTower128ToPoly st.1 ^^^ rustGf128Mul (psiTower128ToPoly st.2) gf128MdsAPolyBits,
       psiTower128ToPoly st.2 ^^^ rustGf128Mul (psiTower128ToPoly st.1) gf128MdsBPolyBits) := by
  apply Prod.ext
  · show psiTower128ToPoly (towerAdd 7 st.1 (towerMul 7 gf128MdsATower st.2)) =
      psiTower128ToPoly st.1 ^^^ rustGf128Mul (psiTower128ToPoly st.2) gf128MdsAPolyBits
    rw [psiTower128ToPoly_add, psiTower128ToPoly_mul_rust, gf128_mds_constants_certified.1,
      rustGf128Mul_comm gf128MdsAPolyBits]
  · show psiTower128ToPoly (towerAdd 7 st.2 (towerMul 7 gf128MdsBTower st.1)) =
      psiTower128ToPoly st.2 ^^^ rustGf128Mul (psiTower128ToPoly st.1) gf128MdsBPolyBits
    rw [psiTower128ToPoly_add, psiTower128ToPoly_mul_rust, gf128_mds_constants_certified.2.1,
      rustGf128Mul_comm gf128MdsBPolyBits]

theorem psiTower128Pair_spnRound128 (rc st : Tower128 × Tower128) :
    psiTower128Pair (spnRound128 gf128MdsATower gf128MdsBTower rc st) =
      rustSpnRound (psiTower128Pair rc) (psiTower128Pair st) := by
  unfold spnRound128
  rw [psiTower128Pair_spnLinearMix]
  show (psiTower128ToPoly (towerSbox7 7 (towerAdd 7 st.1 rc.1)) ^^^
        rustGf128Mul (psiTower128ToPoly (towerSbox7 7 (towerAdd 7 st.2 rc.2))) gf128MdsAPolyBits,
      psiTower128ToPoly (towerSbox7 7 (towerAdd 7 st.2 rc.2)) ^^^
        rustGf128Mul (psiTower128ToPoly (towerSbox7 7 (towerAdd 7 st.1 rc.1))) gf128MdsBPolyBits) =
    (rustPow7 (psiTower128ToPoly st.1 ^^^ psiTower128ToPoly rc.1) ^^^
        rustGf128Mul (rustPow7 (psiTower128ToPoly st.2 ^^^ psiTower128ToPoly rc.2))
          gf128MdsAPolyBits,
      rustPow7 (psiTower128ToPoly st.2 ^^^ psiTower128ToPoly rc.2) ^^^
        rustGf128Mul (rustPow7 (psiTower128ToPoly st.1 ^^^ psiTower128ToPoly rc.1))
          gf128MdsBPolyBits)
  rw [psiTower128ToPoly_sbox7, psiTower128ToPoly_sbox7, psiTower128ToPoly_add,
    psiTower128ToPoly_add]

theorem psiTower128Pair_spnIterRounds128 (rcs : Nat → Tower128 × Tower128) :
    ∀ (r : Nat) (st : Tower128 × Tower128),
      psiTower128Pair (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r st) =
        rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair st)
  | 0, _ => rfl
  | r + 1, st => by
    show psiTower128Pair (spnRound128 gf128MdsATower gf128MdsBTower (rcs r)
        (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r st)) =
      rustSpnRound (psiTower128Pair (rcs r))
        (rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair st))
    rw [psiTower128Pair_spnRound128, psiTower128Pair_spnIterRounds128 rcs r st]

/-- **Tower SPN ↦ Rust SPN.** The image of the tower Davies–Meyer value is the Rust value on
    the image input with image round constants. -/
theorem psiTower128Pair_spnDaviesMeyer48 (rcs : Nat → Tower128 × Tower128)
    (inp : Tower128 × Tower128) :
    psiTower128Pair (spnDaviesMeyer48 gf128MdsATower gf128MdsBTower rcs inp) =
      rustAlgebraicStep (fun i => psiTower128Pair (rcs i)) (psiTower128Pair inp) := by
  have hIter := psiTower128Pair_spnIterRounds128 rcs spnRounds inp
  apply Prod.ext
  · show psiTower128ToPoly (towerAdd 7
        (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs spnRounds inp).1 inp.1) =
      (rustSpnIter (fun i => psiTower128Pair (rcs i)) spnRounds (psiTower128Pair inp)).1 ^^^
        psiTower128ToPoly inp.1
    rw [psiTower128ToPoly_add, ← hIter]
    rfl
  · show psiTower128ToPoly (towerAdd 7
        (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs spnRounds inp).2 inp.2) =
      (rustSpnIter (fun i => psiTower128Pair (rcs i)) spnRounds (psiTower128Pair inp)).2 ^^^
        psiTower128ToPoly inp.2
    rw [psiTower128ToPoly_add, ← hIter]
    rfl

private theorem psi_comp_inv (rcs : Nat → BitVec 128 × BitVec 128) :
    (fun i => psiTower128Pair (polyToTower128Pair (rcs i))) = rcs :=
  funext fun i => psiTower128Pair_polyToTower128Pair (rcs i)

/-- Rust rounds on arbitrary Rust words are the tower rounds on their preimages. -/
theorem rustSpnIter_eq_tower (rcs : Nat → BitVec 128 × BitVec 128) (r : Nat)
    (st : BitVec 128 × BitVec 128) :
    rustSpnIter rcs r st =
      psiTower128Pair (spnIterRounds128 gf128MdsATower gf128MdsBTower
        (fun i => polyToTower128Pair (rcs i)) r (polyToTower128Pair st)) := by
  rw [psiTower128Pair_spnIterRounds128, psi_comp_inv, psiTower128Pair_polyToTower128Pair]

/-- **Rust SPN = tower SPN, quantified on the Rust side.** For every `u128` input pair and
    every round-constant sequence, `algebraic_step_plain` equals the image of the tower
    `spnDaviesMeyer48` with the certified tower constants. -/
theorem rustAlgebraicStep_eq_tower (rcs : Nat → BitVec 128 × BitVec 128)
    (inp : BitVec 128 × BitVec 128) :
    rustAlgebraicStep rcs inp =
      psiTower128Pair (spnDaviesMeyer48 gf128MdsATower gf128MdsBTower
        (fun i => polyToTower128Pair (rcs i)) (polyToTower128Pair inp)) := by
  rw [psiTower128Pair_spnDaviesMeyer48, psi_comp_inv, psiTower128Pair_polyToTower128Pair]

/-! ## 4. Tower results restated on Rust words -/

/-- `pow7_plain` is a permutation of the `u128` words. -/
theorem rustPow7_bijective : IsBijective rustPow7 :=
  ⟨fun a b h => polyToTower128_injective a b (pow7_tower128_bijective.1 _ _ (by
      rw [← polyToTower128_rustPow7, ← polyToTower128_rustPow7, h])),
   fun b => ⟨psiTower128ToPoly (towerSbox7Inv128 (polyToTower128 b)), by
      rw [← psiTower128ToPoly_sbox7, towerSbox7Inv128_right_inv,
        psiTower128ToPoly_polyToTower128]⟩⟩

/-- Injective maps preserve duplicate-freeness. -/
theorem psiTransport_nodup_map {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => .nil
  | a :: l, .cons hrel htail => by
    refine .cons (fun b hb => ?_) (psiTransport_nodup_map f hf htail)
    obtain ⟨a', ha', hEq⟩ := List.mem_map.mp hb
    intro hab
    exact hrel a' ha' (hf a a' (hab.trans hEq.symm))

/-- Counting a predicate on the image list is counting its pullback. -/
theorem psiTransport_filter_map_length {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ l : List α, ((l.map f).filter p).length = (l.filter (fun a => p (f a))).length
  | [] => rfl
  | a :: l => by
    have ih := psiTransport_filter_map_length f p l
    show ((f a :: l.map f).filter p).length = ((a :: l).filter (fun a => p (f a))).length
    rw [List.filter_cons, List.filter_cons]
    cases h : p (f a)
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]
    · simp only [↓reduceIte, List.length_cons, ih]

private theorem polyToTower128_pow7_diff (x delta : BitVec 128) :
    polyToTower128 (rustPow7 (x ^^^ delta) ^^^ rustPow7 x) =
      towerAdd 7 (towerSbox7 7 (towerAdd 7 (polyToTower128 x) (polyToTower128 delta)))
        (towerSbox7 7 (polyToTower128 x)) := by
  rw [polyToTower128_xor, polyToTower128_rustPow7, polyToTower128_rustPow7, polyToTower128_xor]

/-- **Differential uniformity of `pow7_plain` on Rust words.** For a nonzero input XOR
    difference and any output XOR difference, at most six words of any duplicate-free list
    satisfy the differential. -/
theorem rustPow7_differential_uniformity_le_six (delta outDiff : BitVec 128)
    (hDelta : delta ≠ 0#128) (S : List (BitVec 128)) (hNodup : S.Nodup) :
    (S.filter (fun x => decide (rustPow7 (x ^^^ delta) ^^^ rustPow7 x = outDiff))).length ≤ 6 := by
  have hDeltaT : polyToTower128 delta ≠ towerZero 7 :=
    fun h => hDelta ((polyToTower128_eq_zero_iff delta).mp h)
  have hTower := towerSbox7_differential_uniformity_le_six 7 (polyToTower128 delta)
    (polyToTower128 outDiff) hDeltaT (S.map polyToTower128)
    (psiTransport_nodup_map polyToTower128 polyToTower128_injective hNodup)
  rw [psiTransport_filter_map_length] at hTower
  have hPred : (fun x => decide (rustPow7 (x ^^^ delta) ^^^ rustPow7 x = outDiff)) =
      (fun x => decide (towerAdd 7
        (towerSbox7 7 (towerAdd 7 (polyToTower128 x) (polyToTower128 delta)))
        (towerSbox7 7 (polyToTower128 x)) = polyToTower128 outDiff)) := by
    funext x
    have hIff : (rustPow7 (x ^^^ delta) ^^^ rustPow7 x = outDiff) ↔
        (towerAdd 7 (towerSbox7 7 (towerAdd 7 (polyToTower128 x) (polyToTower128 delta)))
          (towerSbox7 7 (polyToTower128 x)) = polyToTower128 outDiff) := by
      rw [← polyToTower128_pow7_diff]
      exact ⟨fun h => congrArg polyToTower128 h, fun h => polyToTower128_injective _ _ h⟩
    by_cases hp : rustPow7 (x ^^^ delta) ^^^ rustPow7 x = outDiff
    · rw [decide_eq_true hp, decide_eq_true (hIff.mp hp)]
    · rw [decide_eq_false hp, decide_eq_false (fun h => hp (hIff.mpr h))]
  rw [hPred]
  exact hTower

/-- Number of nonzero lanes of a Rust XOR difference. -/
def rustLaneActiveWeight (d : BitVec 128 × BitVec 128) : Nat :=
  (if d.1 = 0#128 then 0 else 1) + (if d.2 = 0#128 then 0 else 1)

/-- Active S-boxes of two Rust executions over the first `r` rounds: nonzero lanes of the XOR
    difference entering each round. -/
def rustSpnTrailActiveSboxes (rcs : Nat → BitVec 128 × BitVec 128) :
    Nat → BitVec 128 × BitVec 128 → BitVec 128 × BitVec 128 → Nat
  | 0, _, _ => 0
  | r + 1, s, s' =>
    let cur := rustSpnIter rcs r s
    let cur' := rustSpnIter rcs r s'
    rustSpnTrailActiveSboxes rcs r s s' +
      rustLaneActiveWeight (cur.1 ^^^ cur'.1, cur.2 ^^^ cur'.2)

set_option linter.unusedSimpArgs false in
private theorem rustLaneActiveWeight_psi_diff (u u' : Tower128 × Tower128) :
    rustLaneActiveWeight
        ((psiTower128Pair u).1 ^^^ (psiTower128Pair u').1,
         (psiTower128Pair u).2 ^^^ (psiTower128Pair u').2) =
      laneActiveWeight 7 (towerAdd 7 u.1 u'.1, towerAdd 7 u.2 u'.2) := by
  have hLane : ∀ a b : Tower128,
      (if psiTower128ToPoly a ^^^ psiTower128ToPoly b = 0#128 then 0 else 1) =
        (if towerAdd 7 a b = towerZero 7 then 0 else 1) := by
    intro a b
    rw [← psiTower128ToPoly_add]
    by_cases h : towerAdd 7 a b = towerZero 7
    · rw [(psiTower128ToPoly_eq_zero_iff _).mpr h]
      simp only [h, ↓reduceIte]
    · have h' : ¬ psiTower128ToPoly (towerAdd 7 a b) = 0#128 :=
        fun h' => h ((psiTower128ToPoly_eq_zero_iff _).mp h')
      simp only [h, h', ↓reduceIte]
  show (if psiTower128ToPoly u.1 ^^^ psiTower128ToPoly u'.1 = 0#128 then 0 else 1) +
      (if psiTower128ToPoly u.2 ^^^ psiTower128ToPoly u'.2 = 0#128 then 0 else 1) =
    (if towerAdd 7 u.1 u'.1 = towerZero 7 then 0 else 1) +
      (if towerAdd 7 u.2 u'.2 = towerZero 7 then 0 else 1)
  rw [hLane, hLane]

theorem rustSpnTrailActiveSboxes_psi (rcs : Nat → Tower128 × Tower128) :
    ∀ (r : Nat) (s s' : Tower128 × Tower128),
      rustSpnTrailActiveSboxes (fun i => psiTower128Pair (rcs i)) r
          (psiTower128Pair s) (psiTower128Pair s') =
        spnTrailActiveSboxes gf128MdsATower gf128MdsBTower rcs r s s'
  | 0, _, _ => rfl
  | r + 1, s, s' => by
    show rustSpnTrailActiveSboxes (fun i => psiTower128Pair (rcs i)) r
          (psiTower128Pair s) (psiTower128Pair s') +
        rustLaneActiveWeight
          ((rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair s)).1 ^^^
            (rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair s')).1,
           (rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair s)).2 ^^^
            (rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair s')).2) =
      spnTrailActiveSboxes gf128MdsATower gf128MdsBTower rcs r s s' +
        laneActiveWeight 7
          (towerAdd 7 (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r s).1
              (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r s').1,
           towerAdd 7 (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r s).2
              (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r s').2)
    rw [rustSpnTrailActiveSboxes_psi rcs r s s', ← psiTower128Pair_spnIterRounds128,
      ← psiTower128Pair_spnIterRounds128, rustLaneActiveWeight_psi_diff]

/-- **At least 72 active S-boxes in the Rust computation.** Two distinct `u128` input pairs
    under the same round constants activate at least 72 `pow7_plain` evaluations across the 48
    rounds. This is a count of nonzero XOR differences, not a probability. -/
theorem rustSpn48_active_sboxes_ge_72 (rcs : Nat → BitVec 128 × BitVec 128)
    (s s' : BitVec 128 × BitVec 128) (hNe : s ≠ s') :
    72 ≤ rustSpnTrailActiveSboxes rcs spnRounds s s' := by
  have hNeT : polyToTower128Pair s ≠ polyToTower128Pair s' :=
    fun h => hNe (polyToTower128Pair_injective s s' h)
  have hTower := (spn48_active_sboxes_ge_72 parallelSeededMdsPair
    (fun i => polyToTower128Pair (rcs i)) (polyToTower128Pair s) (polyToTower128Pair s') hNeT).1
  have hEq := rustSpnTrailActiveSboxes_psi (fun i => polyToTower128Pair (rcs i)) spnRounds
    (polyToTower128Pair s) (polyToTower128Pair s')
  rw [psi_comp_inv, psiTower128Pair_polyToTower128Pair,
    psiTower128Pair_polyToTower128Pair] at hEq
  rw [hEq]
  exact hTower

/-- The 48 Rust rounds before the feed-forward are injective. Nothing is claimed for the
    Davies–Meyer output `rustAlgebraicStep`. -/
theorem rustSpnIter48_injective (rcs : Nat → BitVec 128 × BitVec 128)
    (s s' : BitVec 128 × BitVec 128) (hNe : s ≠ s') :
    rustSpnIter rcs spnRounds s ≠ rustSpnIter rcs spnRounds s' := by
  have hNeT : polyToTower128Pair s ≠ polyToTower128Pair s' :=
    fun h => hNe (polyToTower128Pair_injective s s' h)
  have hTower := (spnIterRounds_even_active_bound parallelSeededMdsPair
    (fun i => polyToTower128Pair (rcs i)) 24 (polyToTower128Pair s) (polyToTower128Pair s')
    hNeT).1
  intro hEq
  rw [rustSpnIter_eq_tower, rustSpnIter_eq_tower] at hEq
  exact hTower (psiTower128Pair_injective _ _ hEq)

/-! ## 5. Little-endian lane framing -/

theorem encodeNatLeBytes_decodeNatLeBytes : ∀ bs : List UInt8,
    encodeNatLeBytes bs.length (decodeNatLeBytes bs) = bs
  | [] => rfl
  | b :: bs => by
    have hb := b.toNat_lt
    have hmod : (b.toNat + 256 * decodeNatLeBytes bs) % 256 = b.toNat := by omega
    have hdiv : (b.toNat + 256 * decodeNatLeBytes bs) / 256 = decodeNatLeBytes bs := by omega
    show UInt8.ofNat ((b.toNat + 256 * decodeNatLeBytes bs) % 256) ::
        encodeNatLeBytes bs.length ((b.toNat + 256 * decodeNatLeBytes bs) / 256) = b :: bs
    rw [hmod, hdiv, UInt8.ofNat_toNat, encodeNatLeBytes_decodeNatLeBytes bs]

theorem decodeNatLeBytes_lt : ∀ bs : List UInt8, decodeNatLeBytes bs < 256 ^ bs.length
  | [] => Nat.zero_lt_one
  | b :: bs => by
    have hb := b.toNat_lt
    have ih := decodeNatLeBytes_lt bs
    show b.toNat + 256 * decodeNatLeBytes bs < 256 ^ (bs.length + 1)
    rw [Nat.pow_succ]
    omega

/-- `u128::from_le_bytes`: byte `i` holds coefficients `x^(8i) … x^(8i+7)`, least significant
    bit first. -/
def rustU128FromLeBytes (bs : List UInt8) : BitVec 128 := BitVec.ofNat 128 (decodeNatLeBytes bs)

/-- `u128::to_le_bytes`. -/
def rustU128ToLeBytes (v : BitVec 128) : List UInt8 := encodeNatLeBytes 16 v.toNat

private theorem pow256_16 : (256 : Nat) ^ 16 = 2 ^ 128 := by decide

theorem rustU128ToLeBytes_length (v : BitVec 128) : (rustU128ToLeBytes v).length = 16 :=
  encodeNatLeBytes_length 16 v.toNat

theorem rustU128FromLeBytes_toLeBytes (v : BitVec 128) :
    rustU128FromLeBytes (rustU128ToLeBytes v) = v := by
  unfold rustU128FromLeBytes rustU128ToLeBytes
  rw [decodeNatLeBytes_encodeNatLeBytes 16 v.toNat (pow256_16 ▸ v.isLt)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt v.isLt

theorem rustU128ToLeBytes_fromLeBytes (bs : List UInt8) (hLen : bs.length = 16) :
    rustU128ToLeBytes (rustU128FromLeBytes bs) = bs := by
  have hLt : decodeNatLeBytes bs < 2 ^ 128 := by
    have h := decodeNatLeBytes_lt bs
    rw [hLen, pow256_16] at h
    exact h
  have hRound := encodeNatLeBytes_decodeNatLeBytes bs
  rw [hLen] at hRound
  unfold rustU128ToLeBytes rustU128FromLeBytes
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLt]
  exact hRound

/-- `bytes32_to_lanes` (`parallel_mpc.rs:495`): lane 0 from bytes `0..16`, lane 1 from
    bytes `16..32`. -/
def rustBytes32ToLanes (b : List UInt8) : BitVec 128 × BitVec 128 :=
  (rustU128FromLeBytes (b.take 16), rustU128FromLeBytes (b.drop 16))

/-- `lanes_to_bytes32` (`parallel_mpc.rs:503`). -/
def rustLanesToBytes32 (l : BitVec 128 × BitVec 128) : List UInt8 :=
  rustU128ToLeBytes l.1 ++ rustU128ToLeBytes l.2

private theorem take_append_length_self {α : Type} : ∀ (l₁ l₂ : List α),
    (l₁ ++ l₂).take l₁.length = l₁
  | [], _ => rfl
  | a :: l₁, l₂ => congrArg (a :: ·) (take_append_length_self l₁ l₂)

private theorem drop_append_length_self {α : Type} : ∀ (l₁ l₂ : List α),
    (l₁ ++ l₂).drop l₁.length = l₂
  | [], _ => rfl
  | _ :: l₁, l₂ => drop_append_length_self l₁ l₂

theorem rustLanesToBytes32_length (l : BitVec 128 × BitVec 128) :
    (rustLanesToBytes32 l).length = 32 := by
  unfold rustLanesToBytes32
  rw [List.length_append, rustU128ToLeBytes_length, rustU128ToLeBytes_length]

theorem rustBytes32ToLanes_lanesToBytes32 (l : BitVec 128 × BitVec 128) :
    rustBytes32ToLanes (rustLanesToBytes32 l) = l := by
  have hTake := take_append_length_self (rustU128ToLeBytes l.1) (rustU128ToLeBytes l.2)
  have hDrop := drop_append_length_self (rustU128ToLeBytes l.1) (rustU128ToLeBytes l.2)
  rw [rustU128ToLeBytes_length] at hTake hDrop
  apply Prod.ext
  · show rustU128FromLeBytes ((rustU128ToLeBytes l.1 ++ rustU128ToLeBytes l.2).take 16) = l.1
    rw [hTake, rustU128FromLeBytes_toLeBytes]
  · show rustU128FromLeBytes ((rustU128ToLeBytes l.1 ++ rustU128ToLeBytes l.2).drop 16) = l.2
    rw [hDrop, rustU128FromLeBytes_toLeBytes]

theorem rustLanesToBytes32_bytes32ToLanes (b : List UInt8) (hLen : b.length = 32) :
    rustLanesToBytes32 (rustBytes32ToLanes b) = b := by
  have hT : (b.take 16).length = 16 := by rw [List.length_take, hLen]; rfl
  have hD : (b.drop 16).length = 16 := by rw [List.length_drop, hLen]
  show rustU128ToLeBytes (rustU128FromLeBytes (b.take 16)) ++
    rustU128ToLeBytes (rustU128FromLeBytes (b.drop 16)) = b
  rw [rustU128ToLeBytes_fromLeBytes _ hT, rustU128ToLeBytes_fromLeBytes _ hD,
    List.take_append_drop]

/-! ## 6. `round_constants`, `derive_chain_tweak` and `parallel_chain_step` framing

The 32-byte hash is a parameter `hash32 customization frames`. Rust uses
`cshake256_framed_32`, modelled by `cshake256FramedBytes` in `ThresholdMlDsaAndToprf`; that
module is not imported here and nothing below depends on properties of the hash. -/

/-- ASCII `QSAG.PSFTS.POW7_ROUND.V4`. -/
def spnPow7RoundCustomization : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2e, 0x50, 0x4f, 0x57, 0x37,
   0x5f, 0x52, 0x4f, 0x55, 0x4e, 0x44, 0x2e, 0x56, 0x34]

/-- ASCII `QSAG.PSFTS.CHAIN_TWK.V2`. -/
def spnChainTweakCustomization : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2e, 0x43, 0x48, 0x41, 0x49,
   0x4e, 0x5f, 0x54, 0x57, 0x4b, 0x2e, 0x56, 0x32]

/-- `round_constants(c0, c1, round)` (`parallel_mpc.rs:516`): frames `c0.to_le_bytes()`,
    `c1.to_le_bytes()`, `(round as u32).to_be_bytes()`. -/
def rustSpnRoundConstants (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (c : BitVec 128 × BitVec 128) (round : Nat) : BitVec 128 × BitVec 128 :=
  rustBytes32ToLanes (hash32 spnPow7RoundCustomization
    [rustU128ToLeBytes c.1, rustU128ToLeBytes c.2, be 4 round])

/-- `derive_chain_tweak` (`parallel_mpc.rs:552`): frames `pk_seed`, `epoch` (u32 BE),
    `chain_idx` (u16 BE), `[step]`. -/
def rustDeriveChainTweak (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) : BitVec 128 × BitVec 128 :=
  rustBytes32ToLanes (hash32 spnChainTweakCustomization
    [pkSeed, be 4 epoch, be 2 chainIdx, [step]])

/-- `parallel_chain_step` (`parallel_mpc.rs:585`) on 32-byte chain nodes. -/
def rustParallelChainStep (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) (cur : List UInt8) :
    List UInt8 :=
  rustLanesToBytes32
    (rustAlgebraicStep
      (rustSpnRoundConstants hash32 (rustDeriveChainTweak hash32 pkSeed epoch chainIdx step))
      (rustBytes32ToLanes cur))

/-- **Byte-level chain step = framed tower Davies–Meyer**, for any hash and any bytes. -/
theorem rustParallelChainStep_eq_tower
    (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) (cur : List UInt8) :
    rustParallelChainStep hash32 pkSeed epoch chainIdx step cur =
      rustLanesToBytes32 (psiTower128Pair
        (spnDaviesMeyer48 gf128MdsATower gf128MdsBTower
          (fun i => polyToTower128Pair
            (rustSpnRoundConstants hash32
              (rustDeriveChainTweak hash32 pkSeed epoch chainIdx step) i))
          (polyToTower128Pair (rustBytes32ToLanes cur)))) := by
  unfold rustParallelChainStep
  rw [rustAlgebraicStep_eq_tower]

theorem rustParallelChainStep_length
    (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) (cur : List UInt8) :
    (rustParallelChainStep hash32 pkSeed epoch chainIdx step cur).length = 32 :=
  rustLanesToBytes32_length _


end Qsag
end


section
namespace Qsag
set_option autoImplicit false

/-- Cartesian prefixing: each fresh choice is paired with every remaining assignment. -/
def prefixAssignments {α : Type} (choices : List α) (tails : List (List α)) : List (List α) :=
  choices.flatMap fun x => tails.map (x :: ·)

theorem prefixAssignments_length {α : Type} (choices : List α) (tails : List (List α)) :
    (prefixAssignments choices tails).length = choices.length * tails.length := by
  induction choices with
  | nil => simp [prefixAssignments]
  | cons x xs ih =>
    simp only [prefixAssignments, List.flatMap_cons, List.length_append, List.length_map]
    change tails.length + (prefixAssignments xs tails).length = _
    rw [ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- Uniform Cartesian sample space: a fresh choice at every gate. -/
def freshInputAssignments {α : Type} (inputs : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => prefixAssignments inputs (freshInputAssignments inputs n)

theorem freshInputAssignments_length {α : Type} (inputs : List α) (n : Nat) :
    (freshInputAssignments inputs n).length = inputs.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [freshInputAssignments, prefixAssignments_length, ih, Nat.pow_succ, Nat.mul_comm]

/-- All successful assignments in an experiment with one fresh input per active gate.
    Each gate specifies its nonzero input difference and desired output difference. -/

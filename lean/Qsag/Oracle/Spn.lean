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

/-- `pow7_plain`: `x2 = x·x`, `x4 = x2·x2`, `(x·x2)·x4`. -/
def rustPow7 (x : BitVec 128) : BitVec 128 :=
  let x2 := rustGf128Mul x x
  let x4 := rustGf128Mul x2 x2
  rustGf128Mul (rustGf128Mul x x2) x4

/-- One iteration of the loop in `algebraic_step_plain`. -/
def rustSpnRound (rc st : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  let x7 := rustPow7 (st.1 ^^^ rc.1)
  let y7 := rustPow7 (st.2 ^^^ rc.2)
  (x7 ^^^ rustGf128Mul y7 gf128MdsAPolyBits, y7 ^^^ rustGf128Mul x7 gf128MdsBPolyBits)

/-- The first `r` loop iterations; `rcs round` is `round_constants(c0, c1)[round]`. -/
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

/-- `bytes32_to_lanes`: lane 0 from bytes `0..16`, lane 1 from
    bytes `16..32`. -/
def rustBytes32ToLanes (b : List UInt8) : BitVec 128 × BitVec 128 :=
  (rustU128FromLeBytes (b.take 16), rustU128FromLeBytes (b.drop 16))

/-- `lanes_to_bytes32`. -/
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

The framed extendable-output function is a parameter `framedXof customization frames outLen`.
Rust uses `cshake256_framed_xof` (`qsag-accel/src/keccak.rs`); `cshake256_framed_32` is the same
function at `outLen = 32`. Nothing below depends on properties of the function.

Round constants (`round_constants`, label `POW7_ROUNDS.V5`): ONE stream of `SPN_ROUNDS * 32`
bytes is squeezed from the frames `c0`, `c1`, `SPN_ROUNDS as u32`, and round `i` reads bytes
`[32 i, 32 i + 32)` of it. The round index is not absorbed. -/

/-- ASCII `QSAG.PSFTS.POW7_ROUNDS.V5` (25 bytes). -/
def spnPow7RoundsCustomization : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2e, 0x50, 0x4f, 0x57, 0x37,
   0x5f, 0x52, 0x4f, 0x55, 0x4e, 0x44, 0x53, 0x2e, 0x56, 0x35]

/-- The `SPN_ROUNDS * 32`-byte stream of `round_constants(c0, c1)`. -/
def rustSpnRoundConstantStream (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8)
    (c : BitVec 128 × BitVec 128) : List UInt8 :=
  framedXof spnPow7RoundsCustomization
    [rustU128ToLeBytes c.1, rustU128ToLeBytes c.2, be 4 spnRounds] (spnRounds * 32)

/-- ASCII `QSAG.PSFTS.CHAIN_TWK.V2`. -/
def spnChainTweakCustomization : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2e, 0x43, 0x48, 0x41, 0x49,
   0x4e, 0x5f, 0x54, 0x57, 0x4b, 0x2e, 0x56, 0x32]

/-- `round_constants(c0, c1)[round]`: the `round`-th 32-byte chunk of the stream, read as two
    little-endian lanes. -/
def rustSpnRoundConstants (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8)
    (c : BitVec 128 × BitVec 128) (round : Nat) : BitVec 128 × BitVec 128 :=
  rustBytes32ToLanes (((rustSpnRoundConstantStream framedXof c).drop (32 * round)).take 32)

theorem rustSpnRoundConstants_eq (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8)
    (c : BitVec 128 × BitVec 128) (round : Nat) :
    rustSpnRoundConstants framedXof c round =
      rustBytes32ToLanes (((framedXof spnPow7RoundsCustomization
        [rustU128ToLeBytes c.1, rustU128ToLeBytes c.2, be 4 spnRounds]
        (spnRounds * 32)).drop (32 * round)).take 32) := by rfl

/-- `derive_chain_tweak`: frames `pk_seed`, `epoch` (u32 BE), `chain_idx` (u16 BE), `[step]`;
    32 output bytes. -/
def rustDeriveChainTweak (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) : BitVec 128 × BitVec 128 :=
  rustBytes32ToLanes (framedXof spnChainTweakCustomization
    [pkSeed, be 4 epoch, be 2 chainIdx, [step]] 32)

/-- `parallel_chain_step` on 32-byte chain nodes. -/
def rustParallelChainStep (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) (cur : List UInt8) :
    List UInt8 :=
  rustLanesToBytes32
    (rustAlgebraicStep
      (rustSpnRoundConstants framedXof (rustDeriveChainTweak framedXof pkSeed epoch chainIdx step))
      (rustBytes32ToLanes cur))

/-- **Byte-level chain step = framed tower Davies–Meyer**, for any framed XOF and any bytes. -/
theorem rustParallelChainStep_eq_tower
    (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) (cur : List UInt8) :
    rustParallelChainStep framedXof pkSeed epoch chainIdx step cur =
      rustLanesToBytes32 (psiTower128Pair
        (spnDaviesMeyer48 gf128MdsATower gf128MdsBTower
          (fun i => polyToTower128Pair
            (rustSpnRoundConstants framedXof
              (rustDeriveChainTweak framedXof pkSeed epoch chainIdx step) i))
          (polyToTower128Pair (rustBytes32ToLanes cur)))) := by
  unfold rustParallelChainStep
  rw [rustAlgebraicStep_eq_tower]

theorem rustParallelChainStep_length
    (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) (cur : List UInt8) :
    (rustParallelChainStep framedXof pkSeed epoch chainIdx step cur).length = 32 :=
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
def freshSboxAssignments (inputs : List Tower128) :
    List (Tower128 × Tower128) → List (List Tower128)
  | [] => [[]]
  | (delta, outDiff) :: gates =>
    prefixAssignments
      (inputs.filter fun x => decide
        (towerAdd 7 (towerSbox7 7 (towerAdd 7 x delta)) (towerSbox7 7 x) = outDiff))
      (freshSboxAssignments inputs gates)

/-- Component root bounds give an actual cardinality bound for the fresh-input experiment.
    Its uniform Cartesian sample space has `inputs.length ^ gates.length` elements, so the
    success fraction is at most `6^gates.length / inputs.length^gates.length` when nonempty.
    No corresponding independence assertion is made for the deployed fixed SPN. -/
theorem freshSboxAssignments_length_le (inputs : List Tower128) (hNd : inputs.Nodup)
    (gates : List (Tower128 × Tower128))
    (hNonzero : ∀ gate ∈ gates, gate.1 ≠ towerZero 7) :
    (freshSboxAssignments inputs gates).length ≤ 6 ^ gates.length := by
  induction gates with
  | nil => simp [freshSboxAssignments]
  | cons gate gates ih =>
    rcases gate with ⟨delta, outDiff⟩
    rw [freshSboxAssignments, prefixAssignments_length]
    have hRoot := towerSbox7_differential_uniformity_le_six 7 delta outDiff
      (hNonzero (delta, outDiff) (by simp)) inputs hNd
    have hTail := ih (fun gate hg => hNonzero gate (List.mem_cons_of_mem _ hg))
    simpa [Nat.pow_succ, Nat.mul_comm] using Nat.mul_le_mul hRoot hTail

/-- Reusing one input at two identical tests does not square its acceptance fraction.
    This small exact experiment has each marginal `1/2`, but joint probability `1/2 > 1/4`. -/
theorem repeated_test_does_not_multiply :
    ([false, true].filter id).length = 1 ∧
    ([false, true].filter fun b => b && b).length = 1 ∧
    1 * 2 < 1 * 4 := by decide

/-- A realized trace on a finite uniform input space has at least one accepting input. -/
theorem realized_trace_has_positive_count {α β : Type} [DecidableEq β]
    (coins : List α) (trace : α → β) (x : α) (hx : x ∈ coins) :
    0 < (coins.filter fun y => decide (trace y = trace x)).length := by
  have hm : x ∈ coins.filter (fun y => decide (trace y = trace x)) := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hx, trivial⟩
  cases he : coins.filter (fun y => decide (trace y = trace x)) with
  | nil => rw [he] at hm; cases hm
  | cons a rest => simp

/-- No bound strictly below one atom can bound every realized deterministic trace.
    The inequality `num * coins.length < den` says `num/den < 1/coins.length`.
    The rejected inequality is the cross-multiplied claim that this trace has probability
    at most `num/den`. This applies to any actual fixed-round SPN/Poseidon trace function. -/
theorem realized_trace_refutes_subatom_bound {α β : Type} [DecidableEq β]
    (coins : List α) (trace : α → β) (x : α) (hx : x ∈ coins)
    (num den : Nat) (hSmall : num * coins.length < den) :
    ¬ (coins.filter fun y => decide (trace y = trace x)).length * den ≤ num * coins.length := by
  have hPositive := realized_trace_has_positive_count coins trace x hx
  have hFloor : den ≤ (coins.filter fun y => decide (trace y = trace x)).length * den := by
    simpa using Nat.mul_le_mul_right den hPositive
  omega

/-- Differential trajectory of the actual 48-round tower SPN with fixed constants. -/
def fixedSpnDifferenceTrace (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128)
    (delta input : Tower128 × Tower128) : List (Tower128 × Tower128) :=
  (List.range 49).map fun r =>
    let a := spnIterRounds128 mdsA mdsB rcs r input
    let b := spnIterRounds128 mdsA mdsB rcs r
      (towerAdd 7 input.1 delta.1, towerAdd 7 input.2 delta.2)
    (towerAdd 7 a.1 b.1, towerAdd 7 a.2 b.2)

/-- Concrete obstruction to interpreting the arithmetic product as a fixed-SPN trail bound.
    On a uniform sample list of size `2^256`, every realized differential trajectory has mass
    at least `2^-256`, strictly greater than `(6/2^128)^48`. This does not challenge the valid
    active-box theorem or the separate fresh-input experiment above. -/
theorem fixedSpnDifferenceTrace_not_bounded_by_component_product
    (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128)
    (delta input : Tower128 × Tower128) (coins : List (Tower128 × Tower128))
    (hSize : coins.length = 2 ^ 256) (hInput : input ∈ coins) :
    ¬ (coins.filter fun x => decide
      (fixedSpnDifferenceTrace mdsA mdsB rcs delta x =
        fixedSpnDifferenceTrace mdsA mdsB rcs delta input)).length * (2 ^ 128) ^ 48 ≤
      6 ^ 48 * coins.length := by
  apply realized_trace_refutes_subatom_bound coins
    (fixedSpnDifferenceTrace mdsA mdsB rcs delta) input hInput
  rw [hSize]
  decide


end Qsag
end


section
namespace Qsag
set_option autoImplicit false

/-! ## §1. Finite sums over explicit sample lists -/

/-- Sum of a `Nat`-valued function over a list. -/
def rcSum {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + rcSum f xs

theorem rcSum_le_of_le {α : Type} (f g : α → Nat) (l : List α)
    (h : ∀ x ∈ l, f x ≤ g x) : rcSum f l ≤ rcSum g l := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    exact Nat.add_le_add (h x List.mem_cons_self)
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem rcSum_const {α : Type} (c : Nat) (l : List α) :
    rcSum (fun _ => c) l = l.length * c := by
  induction l with
  | nil => exact (Nat.zero_mul c).symm
  | cons x xs ih =>
    show c + rcSum (fun _ => c) xs = (xs.length + 1) * c
    rw [ih, Nat.succ_mul, Nat.add_comm]

theorem rcSum_le_const {α : Type} (f : α → Nat) (c : Nat) (l : List α)
    (h : ∀ x ∈ l, f x ≤ c) : rcSum f l ≤ l.length * c := by
  rw [← rcSum_const c l]
  exact rcSum_le_of_le f _ l h

theorem rcSum_ite {α : Type} (p : α → Bool) (c : Nat) (l : List α) :
    rcSum (fun x => if p x then c else 0) l = (l.filter p).length * c := by
  induction l with
  | nil => exact (Nat.zero_mul c).symm
  | cons x xs ih =>
    show (if p x then c else 0) + rcSum (fun x => if p x then c else 0) xs = _
    rw [ih]
    cases hp : p x
    · rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]
      exact Nat.zero_add _
    · rw [List.filter_cons_of_pos hp, List.length_cons, Nat.succ_mul, Nat.add_comm]
      rfl

/-- Counting inside a Cartesian prefix: sum over the head of the count over the tails. -/
theorem filter_prefixAssignments_length {α : Type} (p : List α → Bool)
    (choices : List α) (tails : List (List α)) :
    ((prefixAssignments choices tails).filter p).length =
      rcSum (fun x => (tails.filter fun t => p (x :: t)).length) choices := by
  induction choices with
  | nil => rfl
  | cons x xs ih =>
    have hSplit : prefixAssignments (x :: xs) tails =
        tails.map (x :: ·) ++ prefixAssignments xs tails := by
      simp only [prefixAssignments, List.flatMap_cons]
    rw [hSplit, List.filter_append, List.length_append, ih, List.filter_map, List.length_map]
    rfl

theorem mem_freshInputAssignments_length {α : Type} (inputs : List α) :
    ∀ (n : Nat) (l : List α), l ∈ freshInputAssignments inputs n → l.length = n
  | 0, l, h => by
    have hl : l = [] := by simpa [freshInputAssignments] using h
    rw [hl]; rfl
  | n + 1, l, h => by
    simp only [freshInputAssignments, prefixAssignments, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, _, t, ht, rfl⟩ := h
    rw [List.length_cons, mem_freshInputAssignments_length inputs n t ht]

/-- All ordered pairs of lane constants: the sample list for one round. -/
def rcPairs {α : Type} (keys : List α) : List (α × α) :=
  keys.flatMap fun a => keys.map fun b => (a, b)

theorem filter_pairList_length {α : Type} (p : α × α → Bool) (l1 l2 : List α) :
    ((l1.flatMap fun a => l2.map fun b => (a, b)).filter p).length =
      rcSum (fun a => (l2.filter fun b => p (a, b)).length) l1 := by
  induction l1 with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.filter_append, List.length_append, ih, List.filter_map,
      List.length_map]
    rfl

theorem filter_rcPairs_length {α : Type} (p : α × α → Bool) (keys : List α) :
    ((rcPairs keys).filter p).length =
      rcSum (fun a => (keys.filter fun b => p (a, b)).length) keys :=
  filter_pairList_length p keys keys

theorem pairList_length {α : Type} (l1 l2 : List α) :
    (l1.flatMap fun a => l2.map fun b => (a, b)).length = l1.length * l2.length := by
  induction l1 with
  | nil => exact (Nat.zero_mul _).symm
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_map, List.length_cons,
      Nat.succ_mul, Nat.add_comm]

theorem rcPairs_length {α : Type} (keys : List α) :
    (rcPairs keys).length = keys.length * keys.length := pairList_length keys keys

theorem filter_length_eq_zero {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, ¬ p x = true) → (l.filter p).length = 0
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filter_cons_of_neg (h x List.mem_cons_self)]
    exact filter_length_eq_zero p xs fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem filter_singleton_length {α : Type} (p : α → Bool) (a : α) :
    ([a].filter p).length = if p a = true then 1 else 0 := by
  by_cases h : p a = true
  · rw [ite_eq_left h, List.filter_cons_of_pos h]; rfl
  · rw [ite_eq_right h, List.filter_cons_of_neg h]; rfl

theorem rcNodup_map_of_injective {α β : Type} (f : α → β)
    (hInj : ∀ a b, f a = f b → a = b) :
    ∀ l : List α, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    have hx := List.nodup_cons.mp h
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨fun hm => ?_, rcNodup_map_of_injective f hInj xs hx.2⟩
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
    have hEq := hInj _ _ hfy
    rw [hEq] at hy
    exact hx.1 hy

/-! ## §2. One lane and one round -/

theorem tadd_eq_zero_iff (a b : Tower128) : towerAdd 7 a b = towerZero 7 ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h, towerAdd_self_zero]⟩
  have h2 := congrArg (fun z => towerAdd 7 z b) h
  simpa only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] using h2

theorem tadd_shift (t t' k : Tower128) :
    towerAdd 7 (towerAdd 7 t' k) (towerAdd 7 t t') = towerAdd 7 t k := by
  rw [towerAdd_comm 7 t t', towerAdd_comm 7 t' k, towerAdd_assoc, ← towerAdd_assoc 7 t' t' t,
    towerAdd_self_zero, towerZero_add, towerAdd_comm]

theorem tadd_swap (a b c d : Tower128) :
    towerAdd 7 (towerAdd 7 a b) (towerAdd 7 c d) =
      towerAdd 7 (towerAdd 7 a c) (towerAdd 7 b d) := by
  rw [towerAdd_assoc, towerAdd_left_comm 7 b c d, ← towerAdd_assoc]

/-- `a ⊕ b = c ⊕ d` exactly when `a ⊕ c = b ⊕ d`. -/
theorem tadd_cross_iff (a b c d : Tower128) :
    towerAdd 7 a b = towerAdd 7 c d ↔ towerAdd 7 a c = towerAdd 7 b d := by
  rw [← tadd_eq_zero_iff (towerAdd 7 a b), ← tadd_eq_zero_iff (towerAdd 7 a c), tadd_swap]

/-- Output difference of one x^7 gate whose two inputs `t`, `t'` receive the same constant. -/
def sboxLaneDiff (k t t' : Tower128) : Tower128 :=
  towerAdd 7 (towerSbox7 7 (towerAdd 7 t k)) (towerSbox7 7 (towerAdd 7 t' k))

theorem sboxLaneDiff_eq_zero_iff (k t t' : Tower128) :
    sboxLaneDiff k t t' = towerZero 7 ↔ t = t' := by
  rw [sboxLaneDiff, ← tadd_shift t t' k, towerSbox7_diff_zero_iff, tadd_eq_zero_iff]

/-- Number of lane constants producing gate output difference `γ`. -/
def laneCount (keys : List Tower128) (t t' γ : Tower128) : Nat :=
  (keys.filter fun k => decide (sboxLaneDiff k t t' = γ)).length

/-- `6` for an active lane, the whole constant list for an inactive one. -/
def laneBound (N : Nat) (δ : Tower128) : Nat := if δ = towerZero 7 then N else 6

theorem laneCount_le_length (keys : List Tower128) (t t' γ : Tower128) :
    laneCount keys t t' γ ≤ keys.length := List.length_filter_le _ _

/-- The root bound applied to the lane constant: `k ↦ t' ⊕ k` is injective, so the gate
    inputs form a duplicate-free list and `towerSbox7_differential_uniformity_le_six` applies. -/
theorem laneCount_le_laneBound (keys : List Tower128) (hNd : keys.Nodup) (t t' γ : Tower128) :
    laneCount keys t t' γ ≤ laneBound keys.length (towerAdd 7 t t') := by
  unfold laneBound
  by_cases h : towerAdd 7 t t' = towerZero 7
  · rw [ite_eq_left h]; exact laneCount_le_length keys t t' γ
  · rw [ite_eq_right h]
    have hMapNd : (keys.map (towerAdd 7 t')).Nodup :=
      rcNodup_map_of_injective _ (fun a b hab => by
        have h2 := congrArg (towerAdd 7 t') hab
        simpa only [towerAdd_cancel] using h2) keys hNd
    have hU := towerSbox7_differential_uniformity_le_six 7 (towerAdd 7 t t') γ h
      (keys.map (towerAdd 7 t')) hMapNd
    rw [List.filter_map, List.length_map] at hU
    refine Nat.le_trans (Nat.le_of_eq ?_) hU
    unfold laneCount
    apply congrArg List.length
    apply List.filter_congr
    intro k _
    exact decide_eq_decide.mpr (by simp only [sboxLaneDiff, tadd_shift])

theorem laneCount_eq_zero_of_ne (keys : List Tower128) (t t' γ : Tower128)
    (h : ∀ k, sboxLaneDiff k t t' ≠ γ) : laneCount keys t t' γ = 0 := by
  exact filter_length_eq_zero _ keys fun k _ hk => h k (of_decide_eq_true hk)

/-- An inactive lane never produces a zero-to-nonzero or nonzero-to-zero transition, so a
    lane is bounded by six whenever its target or its input difference is nonzero. -/
theorem laneCount_le_six (keys : List Tower128) (hNd : keys.Nodup) (t t' γ : Tower128)
    (h : γ ≠ towerZero 7 ∨ t ≠ t') : laneCount keys t t' γ ≤ 6 := by
  by_cases hT : t = t'
  · have hγ : γ ≠ towerZero 7 := h.elim id (fun hne => absurd hT hne)
    rw [laneCount_eq_zero_of_ne keys t t' γ (fun k hk =>
      hγ (hk ▸ (sboxLaneDiff_eq_zero_iff k t t').mpr hT))]
    exact Nat.zero_le 6
  · have hB := laneCount_le_laneBound keys hNd t t' γ
    unfold laneBound at hB
    rwa [ite_eq_right (fun h0 => hT ((tadd_eq_zero_iff t t').mp h0))] at hB

theorem laneCount_zero_target (keys : List Tower128) (t t' : Tower128) (hT : t ≠ t') :
    laneCount keys t t' (towerZero 7) = 0 :=
  laneCount_eq_zero_of_ne keys t t' _ fun k hk => hT ((sboxLaneDiff_eq_zero_iff k t t').mp hk)

/-- Lanewise xor of two states. -/
def pairXor (a b : Tower128 × Tower128) : Tower128 × Tower128 :=
  (towerAdd 7 a.1 b.1, towerAdd 7 a.2 b.2)

theorem pairXor_ne_zero {s s' : Tower128 × Tower128} (h : s ≠ s') :
    pairXor s s' ≠ (towerZero 7, towerZero 7) := fun h0 =>
  h (Prod.ext ((tadd_eq_zero_iff _ _).mp (congrArg Prod.fst h0))
    ((tadd_eq_zero_iff _ _).mp (congrArg Prod.snd h0)))

/-- Difference of the two states after the constant addition and the x^7 layer. -/
def sboxPairDiff (rc s s' : Tower128 × Tower128) : Tower128 × Tower128 :=
  (sboxLaneDiff rc.1 s.1 s'.1, sboxLaneDiff rc.2 s.2 s'.2)

theorem spnLinearMix_xor (mdsA mdsB : Tower128) (a b : Tower128 × Tower128) :
    pairXor (spnLinearMix 7 mdsA mdsB a) (spnLinearMix 7 mdsA mdsB b) =
      spnLinearMix 7 mdsA mdsB (pairXor a b) := by
  unfold spnLinearMix pairXor
  apply Prod.ext <;> simp only [towerMul_add_distrib, towerAdd_assoc, towerAdd_left_comm]

/-- The state difference after one actual round is the linear layer applied to the S-box
    output difference. The round constant enters only through `sboxPairDiff`. -/
theorem spnRound128_diff (mdsA mdsB : Tower128) (rc s s' : Tower128 × Tower128) :
    pairXor (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s') =
      spnLinearMix 7 mdsA mdsB (sboxPairDiff rc s s') := by
  unfold spnRound128
  rw [spnLinearMix_xor]
  rfl

theorem spnLinearMix_injective (mds : ValidSpnMdsPair 7) (a b : Tower128 × Tower128)
    (h : spnLinearMix 7 mds.mdsA mds.mdsB a = spnLinearMix 7 mds.mdsA mds.mdsB b) : a = b := by
  if hab : a = b then exact hab else
    have hNe := (spnLinearMix_branch_number_three mds (pairXor a b) (pairXor_ne_zero hab)).1
    rw [← spnLinearMix_xor, h] at hNe
    exact absurd (by unfold pairXor; rw [towerAdd_self_zero, towerAdd_self_zero]) hNe

theorem spnRound128_ne (mds : ValidSpnMdsPair 7) (rc s s' : Tower128 × Tower128)
    (h : s ≠ s') : spnRound128 mds.mdsA mds.mdsB rc s ≠ spnRound128 mds.mdsA mds.mdsB rc s' := by
  intro hEq
  have hD := spnRound128_diff mds.mdsA mds.mdsB rc s s'
  rw [hEq] at hD
  have hZero : spnLinearMix 7 mds.mdsA mds.mdsB (sboxPairDiff rc s s') =
      spnLinearMix 7 mds.mdsA mds.mdsB (towerZero 7, towerZero 7) := by
    rw [← hD]; unfold pairXor spnLinearMix
    simp only [towerAdd_self_zero, towerMul_zero]
  have hS := spnLinearMix_injective mds _ _ hZero
  exact h (Prod.ext ((sboxLaneDiff_eq_zero_iff _ _ _).mp (congrArg Prod.fst hS))
    ((sboxLaneDiff_eq_zero_iff _ _ _).mp (congrArg Prod.snd hS)))

/-- One round, exact: the constants producing S-box output difference `γ` form a rectangle,
    because the two lane constants are separate coordinates of the sample. -/
theorem sboxPairDiff_count (keys : List Tower128) (s s' γ : Tower128 × Tower128) :
    ((rcPairs keys).filter fun rc => decide (sboxPairDiff rc s s' = γ)).length =
      laneCount keys s.1 s'.1 γ.1 * laneCount keys s.2 s'.2 γ.2 := by
  rcases γ with ⟨g1, g2⟩
  rw [filter_rcPairs_length]
  have hTerm : (fun a => (keys.filter fun b =>
      decide (sboxPairDiff (a, b) s s' = (g1, g2))).length) =
      fun a => if decide (sboxLaneDiff a s.1 s'.1 = g1) then laneCount keys s.2 s'.2 g2 else 0 := by
    funext a
    by_cases ha : sboxLaneDiff a s.1 s'.1 = g1
    · rw [ite_eq_left (decide_eq_true ha)]
      unfold laneCount
      apply congrArg List.length
      apply List.filter_congr
      intro b _
      simp only [sboxPairDiff, Prod.mk.injEq, ha, true_and]
    · rw [ite_eq_right (fun hd => ha (of_decide_eq_true hd))]
      exact filter_length_eq_zero _ keys fun b _ hb =>
        ha (congrArg Prod.fst (of_decide_eq_true hb))
  rw [hTerm, rcSum_ite]
  rfl

/-! ## §3. Committed trails: the product over rounds, and the adaptive control -/

/-- S-box output differences of the two trajectories, round by round, for the constant list
    `ks` (head = first round). -/
def spnSboxTrail (mdsA mdsB : Tower128) :
    List (Tower128 × Tower128) → Tower128 × Tower128 → Tower128 × Tower128 →
      List (Tower128 × Tower128)
  | [], _, _ => []
  | rc :: rest, s, s' =>
    sboxPairDiff rc s s' ::
      spnSboxTrail mdsA mdsB rest (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s')

/-- Number of constant lists, out of `(N·N)^trail.length`, under which the committed pair
    `s`, `s'` follows the committed trail. -/
def spnTrailCount (keys : List Tower128) (mdsA mdsB : Tower128)
    (s s' : Tower128 × Tower128) (trail : List (Tower128 × Tower128)) : Nat :=
  ((freshInputAssignments (rcPairs keys) trail.length).filter fun ks =>
    decide (spnSboxTrail mdsA mdsB ks s s' = trail)).length

/-- Product of lane bounds along a trail: the input difference of each round is the linear
    layer applied to the previous S-box output difference. -/
def spnTrailBound (N : Nat) (mdsA mdsB : Tower128) :
    Tower128 × Tower128 → List (Tower128 × Tower128) → Nat
  | _, [] => 1
  | δ, γ :: rest =>
    laneBound N δ.1 * laneBound N δ.2 * spnTrailBound N mdsA mdsB (spnLinearMix 7 mdsA mdsB γ) rest

/-- **Markov product for the actual round function.** For every committed pair and trail, the
    number of independent uniform constant lists that realize the trail is at most the product
    of the per-lane root bounds. Proof: the first round's constants are a separate coordinate
    of the sample, and the bound for the remaining rounds is uniform in the reached states. -/
theorem spnTrailCount_le (keys : List Tower128) (hNd : keys.Nodup) (mdsA mdsB : Tower128) :
    ∀ (trail : List (Tower128 × Tower128)) (s s' : Tower128 × Tower128),
      spnTrailCount keys mdsA mdsB s s' trail ≤
        spnTrailBound keys.length mdsA mdsB (pairXor s s') trail
  | [], s, s' => List.length_filter_le _ [[]]
  | γ :: rest, s, s' => by
    unfold spnTrailCount
    rw [List.length_cons, freshInputAssignments, filter_prefixAssignments_length]
    have hTerm : ∀ rc ∈ rcPairs keys,
        ((freshInputAssignments (rcPairs keys) rest.length).filter fun t =>
          decide (spnSboxTrail mdsA mdsB (rc :: t) s s' = γ :: rest)).length ≤
        if decide (sboxPairDiff rc s s' = γ) then
          spnTrailBound keys.length mdsA mdsB (spnLinearMix 7 mdsA mdsB γ) rest else 0 := by
      intro rc _
      by_cases h : sboxPairDiff rc s s' = γ
      · rw [ite_eq_left (decide_eq_true h)]
        have ih := spnTrailCount_le keys hNd mdsA mdsB rest
          (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s')
        rw [spnRound128_diff, h] at ih
        refine Nat.le_trans (Nat.le_of_eq ?_) ih
        unfold spnTrailCount
        apply congrArg List.length
        apply List.filter_congr
        intro t _
        simp only [spnSboxTrail, h, List.cons.injEq, true_and]
      · rw [ite_eq_right (fun hd => h (of_decide_eq_true hd))]
        exact Nat.le_of_eq (filter_length_eq_zero _ _ fun t _ ht =>
          h (List.head_eq_of_cons_eq (of_decide_eq_true ht)))
    refine Nat.le_trans (rcSum_le_of_le _ _ _ hTerm) ?_
    rw [rcSum_ite, sboxPairDiff_count]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul (laneCount_le_laneBound keys hNd s.1 s'.1 γ.1)
        (laneCount_le_laneBound keys hNd s.2 s'.2 γ.2)) (Nat.le_refl _)

/-- Round-constant schedule read from a list (zero past its end). -/
def rcSchedule : List (Tower128 × Tower128) → Nat → Tower128 × Tower128
  | [], _ => (towerZero 7, towerZero 7)
  | rc :: _, 0 => rc
  | _ :: rest, i + 1 => rcSchedule rest i

theorem spnIterRounds128_succ_head (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128) :
    ∀ (r : Nat) (st : Tower128 × Tower128),
      spnIterRounds128 mdsA mdsB rcs (r + 1) st =
        spnIterRounds128 mdsA mdsB (fun i => rcs (i + 1)) r (spnRound128 mdsA mdsB (rcs 0) st)
  | 0, _ => rfl
  | r + 1, st => by
    show spnRound128 mdsA mdsB (rcs (r + 1)) (spnIterRounds128 mdsA mdsB rcs (r + 1) st) =
      spnRound128 mdsA mdsB (rcs (r + 1))
        (spnIterRounds128 mdsA mdsB (fun i => rcs (i + 1)) r (spnRound128 mdsA mdsB (rcs 0) st))
    rw [spnIterRounds128_succ_head mdsA mdsB rcs r st]

/-- The permutation with the constant list applied head first. -/
def spnRunList (mdsA mdsB : Tower128) :
    List (Tower128 × Tower128) → Tower128 × Tower128 → Tower128 × Tower128
  | [], st => st
  | rc :: rest, st => spnRunList mdsA mdsB rest (spnRound128 mdsA mdsB rc st)

/-- `spnRunList` is the actual `spnIterRounds128` under the list's schedule. -/
theorem spnRunList_eq_iter (mdsA mdsB : Tower128) :
    ∀ (ks : List (Tower128 × Tower128)) (st : Tower128 × Tower128),
      spnRunList mdsA mdsB ks st = spnIterRounds128 mdsA mdsB (rcSchedule ks) ks.length st
  | [], _ => rfl
  | rc :: rest, st => by
    rw [List.length_cons, spnIterRounds128_succ_head]
    exact spnRunList_eq_iter mdsA mdsB rest (spnRound128 mdsA mdsB rc st)

theorem spnTrailActiveSboxes_succ_head (mdsA mdsB : Tower128)
    (rcs : Nat → Tower128 × Tower128) :
    ∀ (r : Nat) (s s' : Tower128 × Tower128),
      spnTrailActiveSboxes mdsA mdsB rcs (r + 1) s s' =
        laneActiveWeight 7 (pairXor s s') +
          spnTrailActiveSboxes mdsA mdsB (fun i => rcs (i + 1)) r
            (spnRound128 mdsA mdsB (rcs 0) s) (spnRound128 mdsA mdsB (rcs 0) s')
  | 0, s, s' => (Nat.zero_add _).trans (Nat.add_zero _).symm
  | r + 1, s, s' => by
    have ih := spnTrailActiveSboxes_succ_head mdsA mdsB rcs r s s'
    show spnTrailActiveSboxes mdsA mdsB rcs (r + 1) s s' +
        laneActiveWeight 7 (pairXor (spnIterRounds128 mdsA mdsB rcs (r + 1) s)
          (spnIterRounds128 mdsA mdsB rcs (r + 1) s')) =
      laneActiveWeight 7 (pairXor s s') +
        (spnTrailActiveSboxes mdsA mdsB (fun i => rcs (i + 1)) r
            (spnRound128 mdsA mdsB (rcs 0) s) (spnRound128 mdsA mdsB (rcs 0) s') +
          laneActiveWeight 7 (pairXor
            (spnIterRounds128 mdsA mdsB (fun i => rcs (i + 1)) r (spnRound128 mdsA mdsB (rcs 0) s))
            (spnIterRounds128 mdsA mdsB (fun i => rcs (i + 1)) r
              (spnRound128 mdsA mdsB (rcs 0) s'))))
    rw [ih, spnIterRounds128_succ_head, spnIterRounds128_succ_head, Nat.add_assoc]

/-- Active S-boxes of the two trajectories, counted head first. -/
def spnListActive (mdsA mdsB : Tower128) :
    List (Tower128 × Tower128) → Tower128 × Tower128 → Tower128 × Tower128 → Nat
  | [], _, _ => 0
  | rc :: rest, s, s' =>
    laneActiveWeight 7 (pairXor s s') +
      spnListActive mdsA mdsB rest (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s')

/-- `spnListActive` is the existing `spnTrailActiveSboxes` under the list's schedule. -/
theorem spnListActive_eq (mdsA mdsB : Tower128) :
    ∀ (ks : List (Tower128 × Tower128)) (s s' : Tower128 × Tower128),
      spnListActive mdsA mdsB ks s s' =
        spnTrailActiveSboxes mdsA mdsB (rcSchedule ks) ks.length s s'
  | [], _, _ => rfl
  | rc :: rest, s, s' => by
    rw [List.length_cons, spnTrailActiveSboxes_succ_head]
    show _ + spnListActive mdsA mdsB rest _ _ =
      _ + spnTrailActiveSboxes mdsA mdsB (rcSchedule rest) rest.length _ _
    rw [spnListActive_eq mdsA mdsB rest]
    rfl

theorem laneBound_weight (N : Nat) (δ : Tower128 × Tower128) :
    laneBound N δ.1 * laneBound N δ.2 * N ^ laneActiveWeight 7 δ =
      6 ^ laneActiveWeight 7 δ * (N * N) := by
  unfold laneBound laneActiveWeight
  by_cases h1 : δ.1 = towerZero 7 <;> by_cases h2 : δ.2 = towerZero 7
  · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h1, ite_eq_left h2]
    show N * N * 1 = 1 * (N * N)
    rw [Nat.mul_one, Nat.one_mul]
  · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1, ite_eq_right h2]
    show N * 6 * (1 * N) = 1 * 6 * (N * N)
    rw [Nat.one_mul, Nat.one_mul, Nat.mul_comm N 6, Nat.mul_assoc]
  · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]
    show 6 * N * (1 * N) = 1 * 6 * (N * N)
    rw [Nat.one_mul, Nat.one_mul, Nat.mul_assoc]
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2]
    show 6 * 6 * (1 * N * N) = 1 * 6 * 6 * (N * N)
    rw [Nat.one_mul, Nat.one_mul]

theorem trailBound_step_arith (lb tb N w a n : Nat)
    (hw : lb * N ^ w = 6 ^ w * (N * N)) (ih : tb * N ^ a = 6 ^ a * (N * N) ^ n) :
    lb * tb * N ^ (w + a) = 6 ^ (w + a) * (N * N) ^ (n + 1) := by
  rw [Nat.pow_add N, Nat.pow_add 6, Nat.mul_mul_mul_comm, hw, ih, Nat.pow_succ,
    Nat.mul_mul_mul_comm, Nat.mul_comm (N * N) ((N * N) ^ n)]

/-- On a realized trail the bound is exactly `6^a · N^(2n - a)` for the existing active count. -/
theorem spnTrailBound_realized (N : Nat) (mdsA mdsB : Tower128) :
    ∀ (ks : List (Tower128 × Tower128)) (s s' : Tower128 × Tower128),
      spnTrailBound N mdsA mdsB (pairXor s s') (spnSboxTrail mdsA mdsB ks s s') *
          N ^ spnListActive mdsA mdsB ks s s' =
        6 ^ spnListActive mdsA mdsB ks s s' * (N * N) ^ ks.length
  | [], _, _ => rfl
  | rc :: rest, s, s' => by
    have ih := spnTrailBound_realized N mdsA mdsB rest
      (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s')
    rw [spnRound128_diff] at ih
    exact trailBound_step_arith _ _ N _ _ _ (laneBound_weight N (pairXor s s')) ih

theorem committed_trail_arith (c tb N a M : Nat) (hc : c ≤ tb)
    (hR : tb * N ^ a = 6 ^ a * M) (ha : 72 ≤ a) (h6 : 6 ≤ N) :
    c * N ^ 72 ≤ 6 ^ 72 * M := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hNpos : 0 < N ^ e := Nat.pow_pos (Nat.lt_of_lt_of_le (by decide) h6)
  apply Nat.le_of_mul_le_mul_right _ hNpos
  calc c * N ^ 72 * N ^ e ≤ tb * N ^ 72 * N ^ e :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
    _ = tb * N ^ (72 + e) := by rw [Nat.mul_assoc, ← Nat.pow_add]
    _ = 6 ^ (72 + e) * M := hR
    _ = 6 ^ 72 * M * 6 ^ e := by rw [Nat.pow_add, Nat.mul_right_comm]
    _ ≤ 6 ^ 72 * M * N ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h6 e)

/-- **48 rounds, committed trail.** With the deployed-shape mixing layer, any committed pair
    `s ≠ s'` and committed 48-round trail are realized by at most a `(6/N)^72` fraction of
    the `(N·N)^48` constant lists. This consumes `spn48_active_sboxes_ge_72`: a realized trail
    has at least 72 active lanes, and each active lane costs a factor `6/N`. -/
theorem spn48_committed_trail_count_le (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (hNd : keys.Nodup) (hSix : 6 ≤ keys.length) (s s' : Tower128 × Tower128) (hNe : s ≠ s')
    (trail : List (Tower128 × Tower128)) (hLen : trail.length = spnRounds) :
    spnTrailCount keys mds.mdsA mds.mdsB s s' trail * keys.length ^ 72 ≤
      6 ^ 72 * (keys.length * keys.length) ^ 48 := by
  cases hF : (freshInputAssignments (rcPairs keys) trail.length).filter fun ks =>
      decide (spnSboxTrail mds.mdsA mds.mdsB ks s s' = trail) with
  | nil =>
    unfold spnTrailCount
    rw [hF]
    exact (Nat.zero_mul _).symm ▸ Nat.zero_le _
  | cons ks more =>
    have hMem : ks ∈ (freshInputAssignments (rcPairs keys) trail.length).filter fun ks =>
        decide (spnSboxTrail mds.mdsA mds.mdsB ks s s' = trail) := by
      rw [hF]; exact List.mem_cons_self
    obtain ⟨hIn, hDec⟩ := List.mem_filter.mp hMem
    have hEq : spnSboxTrail mds.mdsA mds.mdsB ks s s' = trail := of_decide_eq_true hDec
    have hLenKs : ks.length = spnRounds :=
      (mem_freshInputAssignments_length _ _ _ hIn).trans hLen
    have hAct : 72 ≤ spnListActive mds.mdsA mds.mdsB ks s s' := by
      rw [spnListActive_eq, hLenKs]
      exact (spn48_active_sboxes_ge_72 mds (rcSchedule ks) s s' hNe).1
    have hR := spnTrailBound_realized keys.length mds.mdsA mds.mdsB ks s s'
    rw [hEq, hLenKs] at hR
    exact committed_trail_arith _ _ _ _ _
      (spnTrailCount_le keys hNd mds.mdsA mds.mdsB trail s s') hR hAct hSix

/-- The committed-trail probability, as a `RatBound` over the `2^128`-element lane constant
    list, is at most `sbox7MaxDiffProb128.pow 72`. This is the event that the arithmetic in
    `spn48_differential_trail_security_bounds` was missing; its third conjunct now applies. -/
theorem spn48_committed_trail_atLeast_256_bits (mds : ValidSpnMdsPair 7)
    (keys : List Tower128) (hNd : keys.Nodup) (hN : keys.length = 2 ^ 128)
    (s s' : Tower128 × Tower128) (hNe : s ≠ s')
    (trail : List (Tower128 × Tower128)) (hLen : trail.length = spnRounds) :
    let prob : RatBound := ⟨spnTrailCount keys mds.mdsA mds.mdsB s s' trail,
      (2 ^ 128 * 2 ^ 128) ^ 48, Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128))⟩
    RatBound.le prob (sbox7MaxDiffProb128.pow 72) ∧ atLeastBits 256 prob := by
  have hLe : RatBound.le
      (⟨spnTrailCount keys mds.mdsA mds.mdsB s s' trail, (2 ^ 128 * 2 ^ 128) ^ 48,
        Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128))⟩ : RatBound)
      (sbox7MaxDiffProb128.pow 72) := by
    have h := spn48_committed_trail_count_le mds keys hNd
      (by rw [hN]; exact Nat.le_of_lt_succ (by decide)) s s' hNe trail hLen
    rw [hN] at h
    exact h
  exact ⟨hLe, atLeastBits_of_le hLe
    (atLeastBits_of_strictlyMoreThanBits spn48_differential_trail_security_bounds.2.2)⟩

/-- **Adaptive control.** A trail selected after the constants are published (here: the trail
    the committed pair actually follows) is realized by every constant list. The committed
    bound therefore says nothing about an attacker who reads the public constants first. -/
theorem spn_adaptive_trail_always_realized (keys : List Tower128) (mdsA mdsB : Tower128)
    (s s' : Tower128 × Tower128) (n : Nat) :
    ((freshInputAssignments (rcPairs keys) n).filter fun ks =>
      decide (spnSboxTrail mdsA mdsB ks s s' =
        (fun seen => spnSboxTrail mdsA mdsB seen s s') ks)).length =
      (keys.length * keys.length) ^ n := by
  have hAll : ((freshInputAssignments (rcPairs keys) n).filter fun ks =>
      decide (spnSboxTrail mdsA mdsB ks s s' =
        (fun seen => spnSboxTrail mdsA mdsB seen s s') ks)) =
      freshInputAssignments (rcPairs keys) n :=
    List.filter_eq_self.mpr fun ks _ => decide_eq_true rfl
  rw [hAll, freshInputAssignments_length, rcPairs_length]

/-- The adaptive count violates the committed 48-round bound for every list of more than six
    lane constants. -/
theorem spn48_adaptive_trail_exceeds_committed_bound (N : Nat) (hN : 6 < N) :
    ¬ (N * N) ^ 48 * N ^ 72 ≤ 6 ^ 72 * (N * N) ^ 48 := by
  intro h
  rw [Nat.mul_comm (6 ^ 72)] at h
  have hPos : 0 < (N * N) ^ 48 :=
    Nat.pow_pos (Nat.mul_pos (Nat.lt_trans (by decide) hN) (Nat.lt_trans (by decide) hN))
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le
    (Nat.pow_lt_pow_left hN (by decide)) (Nat.le_of_mul_le_mul_left h hPos))


end Qsag
end


section
namespace Qsag
set_option autoImplicit false

/-! ## §1. Counting a duplicate-free list of pairs inside a rectangle -/

theorem rcFilter_length_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl 0
  | x :: xs, h => by
    have ih := rcFilter_length_le_of_imp p q xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h x List.mem_cons_self hp)]
      exact Nat.succ_le_succ ih
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q x = true
      · rw [List.filter_cons_of_pos hq]; exact Nat.le_succ_of_le ih
      · rw [List.filter_cons_of_neg hq]; exact ih

theorem rcFilter_split_length {α : Type} (p r : α → Bool) :
    ∀ l : List α, (l.filter p).length =
      (l.filter fun x => p x && r x).length + (l.filter fun x => p x && !r x).length
  | [] => rfl
  | x :: xs => by
    have ih := rcFilter_split_length p r xs
    by_cases hp : p x = true
    · by_cases hr : r x = true
      · have h1 : (p x && r x) = true := by rw [hp, hr]; rfl
        have h2 : ¬ (p x && !r x) = true := by rw [hp, hr]; exact Bool.false_ne_true
        rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (p := fun x => p x && r x) h1,
          List.filter_cons_of_neg (p := fun x => p x && !r x) h2,
          List.length_cons, List.length_cons, ih, Nat.add_right_comm]
      · have hr' : r x = false := Bool.eq_false_iff.mpr hr
        have h1 : ¬ (p x && r x) = true := by rw [hp, hr']; exact Bool.false_ne_true
        have h2 : (p x && !r x) = true := by rw [hp, hr']; rfl
        rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (p := fun x => p x && r x) h1,
          List.filter_cons_of_pos (p := fun x => p x && !r x) h2,
          List.length_cons, List.length_cons, ih, Nat.add_assoc]
    · have hp' : p x = false := Bool.eq_false_iff.mpr hp
      have h1 : ¬ (p x && r x) = true := by rw [hp']; exact Bool.false_ne_true
      have h2 : ¬ (p x && !r x) = true := by rw [hp']; exact Bool.false_ne_true
      rw [List.filter_cons_of_neg hp, List.filter_cons_of_neg (p := fun x => p x && r x) h1,
        List.filter_cons_of_neg (p := fun x => p x && !r x) h2, ih]

theorem nodup_map_snd_of_fst_eq {α : Type} (a : α) :
    ∀ L : List (α × α), L.Nodup → (∀ x ∈ L, x.1 = a) → (L.map Prod.snd).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hNd, hFst => by
    have hx := List.nodup_cons.mp hNd
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨fun hm => ?_,
      nodup_map_snd_of_fst_eq a xs hx.2 fun y hy => hFst y (List.mem_cons_of_mem _ hy)⟩
    obtain ⟨y, hy, hySnd⟩ := List.mem_map.mp hm
    have hyEq : y = x := Prod.ext
      ((hFst y (List.mem_cons_of_mem _ hy)).trans (hFst x List.mem_cons_self).symm) hySnd
    rw [hyEq] at hy
    exact hx.1 hy

/-- If the first coordinates satisfying `p` take at most `m` distinct values and the second
    coordinates satisfying `q` at most `n`, a duplicate-free list of pairs has at most `m·n`
    members in the rectangle `p × q`. No enumeration of the coordinate type is needed. -/
theorem rect_count_le {α : Type} [DecidableEq α] (q : α → Bool) (n : Nat)
    (hq : ∀ S : List α, S.Nodup → (S.filter q).length ≤ n) :
    ∀ (m : Nat) (p : α → Bool), (∀ S : List α, S.Nodup → (S.filter p).length ≤ m) →
      ∀ l : List (α × α), l.Nodup → (l.filter fun x => p x.1 && q x.2).length ≤ m * n
  | 0, p, hp, l, _ => by
    rw [filter_length_eq_zero _ l]
    · exact Nat.zero_le _
    · intro x _ hx
      have hp1 : p x.1 = true := (Bool.and_eq_true_iff.mp hx).1
      have hB := hp [x.1] (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
      rw [List.filter_cons_of_pos hp1] at hB
      exact Nat.not_succ_le_zero _ hB
  | m + 1, p, hp, l, hNd => by
    cases hF : l.filter (fun x => p x.1 && q x.2) with
    | nil => exact Nat.zero_le _
    | cons x0 more =>
      have hx0 : x0 ∈ l.filter (fun x => p x.1 && q x.2) := by rw [hF]; exact List.mem_cons_self
      have hpx0 : p x0.1 = true := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hx0).2).1
      rw [← hF, rcFilter_split_length _ (fun x => decide (x.1 = x0.1)) l]
      have h1 : (l.filter fun x => (p x.1 && q x.2) && decide (x.1 = x0.1)).length ≤ n := by
        have hT : ((l.filter fun x => decide (x.1 = x0.1)).map Prod.snd).Nodup :=
          nodup_map_snd_of_fst_eq x0.1 _ (List.Pairwise.filter _ hNd)
            fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2
        have hB := hq _ hT
        rw [List.filter_map, List.length_map, List.filter_filter] at hB
        refine Nat.le_trans (rcFilter_length_le_of_imp _ _ l fun x _ hx => ?_) hB
        have h3 := Bool.and_eq_true_iff.mp hx
        exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp h3.1).2, h3.2⟩
      have h2 : (l.filter fun x => (p x.1 && q x.2) && !decide (x.1 = x0.1)).length ≤ m * n := by
        refine Nat.le_trans (Nat.le_of_eq ?_)
          (rect_count_le q n hq m (fun a => p a && !decide (a = x0.1)) ?_ l hNd)
        · apply congrArg List.length
          apply List.filter_congr
          intro x _
          show ((p x.1 && q x.2) && !decide (x.1 = x0.1)) =
            ((p x.1 && !decide (x.1 = x0.1)) && q x.2)
          cases p x.1 <;> cases q x.2 <;> cases decide (x.1 = x0.1) <;> rfl
        · intro S hS
          have hNd' : (x0.1 :: S.filter fun a => p a && !decide (a = x0.1)).Nodup :=
            List.nodup_cons.mpr ⟨fun hm => by
              have hb := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hm).2).2
              rw [decide_eq_true rfl] at hb
              exact Bool.false_ne_true hb, List.Pairwise.filter _ hS⟩
          have hB := hp _ hNd'
          have hSelf : (S.filter fun a => p a && !decide (a = x0.1)).filter p =
              S.filter fun a => p a && !decide (a = x0.1) :=
            List.filter_eq_self.mpr fun a ha =>
              (Bool.and_eq_true_iff.mp (List.mem_filter.mp ha).2).1
          rw [List.filter_cons_of_pos hpx0, List.length_cons, hSelf] at hB
          exact Nat.le_of_succ_le_succ hB
      exact Nat.le_trans (Nat.add_le_add h1 h2)
        (Nat.le_of_eq (by rw [Nat.succ_mul, Nat.add_comm]))

/-! ## §2. Lane roots as a function of the input, and one fully active round -/

theorem sboxLaneDiff_input_symm (k a δ : Tower128) :
    sboxLaneDiff k a (towerAdd 7 a δ) = sboxLaneDiff a k (towerAdd 7 k δ) := by
  unfold sboxLaneDiff
  rw [towerAdd_comm 7 a k, towerAdd_assoc 7 a δ k, towerAdd_comm 7 (towerAdd 7 k δ) a,
    towerAdd_comm 7 δ k]

/-- For a fixed lane constant and nonzero difference, at most six lane inputs give a
    prescribed x^7 output difference. Same root bound, with the input as the unknown. -/
theorem laneRoots_le_six (k δ γ : Tower128) (hδ : δ ≠ towerZero 7) (S : List Tower128)
    (hS : S.Nodup) :
    (S.filter fun a => decide (sboxLaneDiff k a (towerAdd 7 a δ) = γ)).length ≤ 6 := by
  have h := laneCount_le_laneBound S hS k (towerAdd 7 k δ) γ
  unfold laneBound at h
  rw [towerAdd_cancel, ite_eq_right hδ] at h
  refine Nat.le_trans (Nat.le_of_eq ?_) h
  unfold laneCount
  apply congrArg List.length
  apply List.filter_congr
  intro a _
  rw [sboxLaneDiff_input_symm]

/-- A fully active S-box layer with fixed constant: at most `36` states of any
    duplicate-free list produce a prescribed output difference. -/
theorem active_layer_states_le_36 (rc δ γ : Tower128 × Tower128)
    (h1 : δ.1 ≠ towerZero 7) (h2 : δ.2 ≠ towerZero 7) (l : List (Tower128 × Tower128))
    (hNd : l.Nodup) :
    (l.filter fun u => decide (sboxPairDiff rc u (pairXor u δ) = γ)).length ≤ 36 := by
  have hR := rect_count_le
    (fun b => decide (sboxLaneDiff rc.2 b (towerAdd 7 b δ.2) = γ.2)) 6
    (fun S hS => laneRoots_le_six rc.2 δ.2 γ.2 h2 S hS) 6
    (fun a => decide (sboxLaneDiff rc.1 a (towerAdd 7 a δ.1) = γ.1))
    (fun S hS => laneRoots_le_six rc.1 δ.1 γ.1 h1 S hS) l hNd
  refine Nat.le_trans (rcFilter_length_le_of_imp _ _ l fun u _ hu => ?_) hR
  have hEq : sboxPairDiff rc u (pairXor u δ) = γ := of_decide_eq_true hu
  exact Bool.and_eq_true_iff.mpr
    ⟨decide_eq_true (congrArg Prod.fst hEq), decide_eq_true (congrArg Prod.snd hEq)⟩

theorem laneActiveWeight_le_one_left (st : Tower128 × Tower128) (h : st.1 = towerZero 7) :
    laneActiveWeight 7 st ≤ 1 := by
  unfold laneActiveWeight
  rw [ite_eq_left h]
  by_cases h2 : st.2 = towerZero 7
  · rw [ite_eq_left h2]; decide
  · rw [ite_eq_right h2]; decide

theorem laneActiveWeight_le_one_right (st : Tower128 × Tower128) (h : st.2 = towerZero 7) :
    laneActiveWeight 7 st ≤ 1 := by
  unfold laneActiveWeight
  rw [ite_eq_left h]
  by_cases h1 : st.1 = towerZero 7
  · rw [ite_eq_left h1]; decide
  · rw [ite_eq_right h1]; decide

theorem pairXor_eq_right {a b c : Tower128 × Tower128} (h : pairXor a b = c) :
    b = pairXor a c := by
  rw [← h]
  unfold pairXor
  exact Prod.ext (towerAdd_cancel 7 a.1 b.1).symm (towerAdd_cancel 7 a.2 b.2).symm

/-! ## §3. Fixed constants: at most 36 inputs follow any trail of two or more rounds -/

/-- **Fixed public constants.** For every constant list `rc1 :: rc2 :: rest` (any values:
    cSHAKE output, zero, adversarial), every nonzero input difference `δ`, every S-box trail
    and every duplicate-free input list, at most `36` inputs `x` make the pair
    `(x, x ⊕ δ)` follow the trail. -/
theorem spn_fixed_constants_trail_count_le (mds : ValidSpnMdsPair 7)
    (rc1 rc2 : Tower128 × Tower128) (rest : List (Tower128 × Tower128))
    (δ : Tower128 × Tower128) (hδ : δ ≠ (towerZero 7, towerZero 7))
    (trail : List (Tower128 × Tower128)) (inputs : List (Tower128 × Tower128))
    (hNd : inputs.Nodup) :
    (inputs.filter fun x => decide
      (spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x (pairXor x δ) = trail)).length ≤ 36 := by
  cases hF : inputs.filter (fun x => decide
      (spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x (pairXor x δ) = trail)) with
  | nil => exact Nat.zero_le _
  | cons x0 more =>
    rw [← hF]
    have hx0 : x0 ∈ inputs.filter (fun x => decide
        (spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x (pairXor x δ) = trail)) := by
      rw [hF]; exact List.mem_cons_self
    have hT0 : spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x0 (pairXor x0 δ) = trail :=
      of_decide_eq_true (List.mem_filter.mp hx0).2
    -- the trail's first two entries, read off the realizing input
    obtain ⟨g1, g2, tl, hTrail⟩ : ∃ g1 g2 tl, trail = g1 :: g2 :: tl := ⟨_, _, _, hT0.symm⟩
    subst hTrail
    have hHead : ∀ x, spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x (pairXor x δ) =
        g1 :: g2 :: tl →
        sboxPairDiff rc1 x (pairXor x δ) = g1 ∧
        sboxPairDiff rc2 (spnRound128 mds.mdsA mds.mdsB rc1 x)
          (pairXor (spnRound128 mds.mdsA mds.mdsB rc1 x) (spnLinearMix 7 mds.mdsA mds.mdsB g1)) =
          g2 := by
      intro x hx
      have hA : sboxPairDiff rc1 x (pairXor x δ) = g1 := List.head_eq_of_cons_eq hx
      have hB : sboxPairDiff rc2 (spnRound128 mds.mdsA mds.mdsB rc1 x)
          (spnRound128 mds.mdsA mds.mdsB rc1 (pairXor x δ)) = g2 :=
        List.head_eq_of_cons_eq (List.tail_eq_of_cons_eq hx)
      have hD := spnRound128_diff mds.mdsA mds.mdsB rc1 x (pairXor x δ)
      rw [hA] at hD
      rw [pairXor_eq_right hD] at hB
      exact ⟨hA, hB⟩
    have hg1 : g1.1 = towerZero 7 ↔ δ.1 = towerZero 7 := by
      rw [← (hHead x0 hT0).1]
      show sboxLaneDiff rc1.1 x0.1 (towerAdd 7 x0.1 δ.1) = towerZero 7 ↔ _
      rw [sboxLaneDiff_eq_zero_iff]
      constructor
      · intro h
        have h2 := congrArg (towerAdd 7 x0.1) h
        rw [towerAdd_self_zero, towerAdd_cancel] at h2
        exact h2.symm
      · intro h; rw [h, towerAdd_zero]
    have hg2 : g1.2 = towerZero 7 ↔ δ.2 = towerZero 7 := by
      rw [← (hHead x0 hT0).1]
      show sboxLaneDiff rc1.2 x0.2 (towerAdd 7 x0.2 δ.2) = towerZero 7 ↔ _
      rw [sboxLaneDiff_eq_zero_iff]
      constructor
      · intro h
        have h2 := congrArg (towerAdd 7 x0.2) h
        rw [towerAdd_self_zero, towerAdd_cancel] at h2
        exact h2.symm
      · intro h; rw [h, towerAdd_zero]
    by_cases hA : δ.1 ≠ towerZero 7 ∧ δ.2 ≠ towerZero 7
    · -- first round fully active
      refine Nat.le_trans (rcFilter_length_le_of_imp _ _ inputs fun x _ hx => ?_)
        (active_layer_states_le_36 rc1 δ g1 hA.1 hA.2 inputs hNd)
      exact decide_eq_true (hHead x (of_decide_eq_true hx)).1
    · -- otherwise the branch number forces the second round to be fully active
      have hg1Ne : g1 ≠ (towerZero 7, towerZero 7) := fun h0 =>
        hδ (Prod.ext (hg1.mp (congrArg Prod.fst h0)) (hg2.mp (congrArg Prod.snd h0)))
      have hBr := (spnLinearMix_branch_number_three mds g1 hg1Ne).2
      have hW1 : laneActiveWeight 7 g1 ≤ 1 := by
        by_cases h1 : δ.1 = towerZero 7
        · exact laneActiveWeight_le_one_left g1 (hg1.mpr h1)
        · by_cases h2 : δ.2 = towerZero 7
          · exact laneActiveWeight_le_one_right g1 (hg2.mpr h2)
          · exact absurd ⟨h1, h2⟩ hA
      have hM1 : (spnLinearMix 7 mds.mdsA mds.mdsB g1).1 ≠ towerZero 7 := fun h0 => by
        have hW := laneActiveWeight_le_one_left _ h0
        omega
      have hM2 : (spnLinearMix 7 mds.mdsA mds.mdsB g1).2 ≠ towerZero 7 := fun h0 => by
        have hW := laneActiveWeight_le_one_right _ h0
        omega
      have hInj : ∀ a b : Tower128 × Tower128,
          spnRound128 mds.mdsA mds.mdsB rc1 a = spnRound128 mds.mdsA mds.mdsB rc1 b → a = b :=
        fun a b hab => if h : a = b then h else absurd hab (spnRound128_ne mds rc1 a b h)
      have hB := active_layer_states_le_36 rc2 (spnLinearMix 7 mds.mdsA mds.mdsB g1) g2 hM1 hM2
        (inputs.map (spnRound128 mds.mdsA mds.mdsB rc1))
        (rcNodup_map_of_injective _ hInj inputs hNd)
      rw [List.filter_map, List.length_map] at hB
      refine Nat.le_trans (rcFilter_length_le_of_imp _ _ inputs fun x _ hx => ?_) hB
      exact decide_eq_true (hHead x (of_decide_eq_true hx)).2

/-- On a `2^256`-element input list the fixed-constant trail probability is at most
    `36 / 2^256 < 2^-250`. Together with the `2^-256` atom floor this locates it; the
    `(6/2^128)^72` product is not a bound for this experiment. -/
theorem spn_fixed_constants_trail_atLeast_250_bits (mds : ValidSpnMdsPair 7)
    (rc1 rc2 : Tower128 × Tower128) (rest : List (Tower128 × Tower128))
    (δ : Tower128 × Tower128) (hδ : δ ≠ (towerZero 7, towerZero 7))
    (trail : List (Tower128 × Tower128)) (inputs : List (Tower128 × Tower128))
    (hNd : inputs.Nodup) :
    atLeastBits 250 ⟨(inputs.filter fun x => decide
      (spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x (pairXor x δ) = trail)).length,
      2 ^ 256, Nat.two_pow_pos 256⟩ :=
  Nat.le_trans (Nat.mul_le_mul_right _
    (spn_fixed_constants_trail_count_le mds rc1 rc2 rest δ hδ trail inputs hNd))
    (show 36 * 2 ^ 250 ≤ 2 ^ 256 by decide)

/-! ## §4. The sample lists exist -/

theorem pairList_nodup {α : Type} (l2 : List α) (h2 : l2.Nodup) :
    ∀ l1 : List α, l1.Nodup → (l1.flatMap fun a => l2.map fun b => (a, b)).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h1 => by
    have hx := List.nodup_cons.mp h1
    rw [List.flatMap_cons]
    refine List.nodup_append.mpr
      ⟨rcNodup_map_of_injective _ (fun a b hab => congrArg Prod.snd hab) l2 h2,
        pairList_nodup l2 h2 xs hx.2, fun u hu v hv huv => ?_⟩
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hu
    obtain ⟨a, ha, hav⟩ := List.mem_flatMap.mp hv
    obtain ⟨c, _, hc⟩ := List.mem_map.mp hav
    have hEq : x = a := by
      have h3 := congrArg Prod.fst huv
      rw [← hb, ← hc] at h3
      exact h3
    rw [← hEq] at ha
    exact hx.1 ha

theorem rcPairs_nodup {α : Type} (keys : List α) (h : keys.Nodup) : (rcPairs keys).Nodup :=
  pairList_nodup keys h keys h

/-- Every element of the level-`k` Wiedemann tower, once. -/
def towerAll : (k : Nat) → List (TowerElem k)
  | 0 => [false, true]
  | k + 1 => rcPairs (towerAll k)

theorem towerAll_length : ∀ k : Nat, (towerAll k).length = 2 ^ 2 ^ k
  | 0 => rfl
  | k + 1 => by
    show (rcPairs (towerAll k)).length = _
    rw [rcPairs_length, towerAll_length k, ← Nat.pow_add, Nat.pow_succ 2 k, Nat.mul_two]

theorem towerAll_nodup : ∀ k : Nat, (towerAll k).Nodup
  | 0 => by decide
  | k + 1 => rcPairs_nodup _ (towerAll_nodup k)

theorem towerAll_complete : ∀ (k : Nat) (x : TowerElem k), x ∈ towerAll k
  | 0, false => List.mem_cons_self
  | 0, true => List.mem_cons_of_mem _ List.mem_cons_self
  | k + 1, x =>
    List.mem_flatMap.mpr ⟨x.1, towerAll_complete k x.1,
      List.mem_map.mpr ⟨x.2, towerAll_complete k x.2, rfl⟩⟩

theorem mem_rcPairs {α : Type} (keys : List α) (x : α × α) (h1 : x.1 ∈ keys)
    (h2 : x.2 ∈ keys) : x ∈ rcPairs keys :=
  List.mem_flatMap.mpr ⟨x.1, h1, List.mem_map.mpr ⟨x.2, h2, rfl⟩⟩

theorem towerAll_length_128 : (towerAll 7).length = 2 ^ 128 := towerAll_length 7

theorem towerAll_pairs_length_256 : (rcPairs (towerAll 7)).length = 2 ^ 256 := by
  rw [rcPairs_length, towerAll_length_128]

/-- The lane-constant list of `2^128` elements and the input list of `2^256` states assumed
    by the experiment theorems exist, are duplicate-free and contain every element. -/
theorem spn_experiment_sample_lists_inhabited :
    (towerAll 7).Nodup ∧ (towerAll 7).length = 2 ^ 128 ∧ (∀ x : Tower128, x ∈ towerAll 7) ∧
    (rcPairs (towerAll 7)).Nodup ∧ (rcPairs (towerAll 7)).length = 2 ^ 256 :=
  ⟨towerAll_nodup 7, towerAll_length_128, towerAll_complete 7,
    rcPairs_nodup _ (towerAll_nodup 7), towerAll_pairs_length_256⟩

/-- Regime 1 on the full lists, deployed mixing constants: a committed 48-round trail under
    uniformly drawn constants has probability below `2^-256`. -/
theorem spn48_full_list_committed_trail_bits
    (s s' : Tower128 × Tower128) (hNe : s ≠ s') (trail : List (Tower128 × Tower128))
    (hLen : trail.length = spnRounds) :
    atLeastBits 256 ⟨spnTrailCount (towerAll 7) parallelSeededMdsPair.mdsA
        parallelSeededMdsPair.mdsB s s' trail, (2 ^ 128 * 2 ^ 128) ^ 48,
      Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128))⟩ :=
  (spn48_committed_trail_atLeast_256_bits parallelSeededMdsPair (towerAll 7) (towerAll_nodup 7)
    towerAll_length_128 s s' hNe trail hLen).2

/-- Regime 2 on the full input list, deployed mixing constants, any fixed round constants:
    at most 36 of the `2^256` inputs follow a given trail. -/
theorem spn48_full_list_fixed_constants_trail_count
    (δ : Tower128 × Tower128) (hδ : δ ≠ (towerZero 7, towerZero 7))
    (trail : List (Tower128 × Tower128))
    (rc1 rc2 : Tower128 × Tower128) (rest : List (Tower128 × Tower128)) :
    ((rcPairs (towerAll 7)).filter fun x => decide
      (spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB (rc1 :: rc2 :: rest)
        x (pairXor x δ) = trail)).length ≤ 36 :=
  spn_fixed_constants_trail_count_le parallelSeededMdsPair rc1 rc2 rest δ hδ trail _
    (rcPairs_nodup _ (towerAll_nodup 7))

/-- Regime 2, both ends, on the full input list: the trail realized by any input `x0` under
    any fixed constants is followed by at least one and at most 36 of the `2^256` inputs.
    (`realized_trace_has_positive_count` is the atom floor of `HashTrailSampling`; the general
    refutation `fixedSpnDifferenceTrace_not_bounded_by_component_product` has its two list
    hypotheses discharged by `spn_experiment_sample_lists_inhabited` and `mem_rcPairs`. The
    count is kept out of `Nat` arithmetic with large literals on purpose: the kernel would try
    to evaluate the enumeration.) -/
theorem spn48_full_list_fixed_constants_trail_sandwich
    (δ : Tower128 × Tower128) (hδ : δ ≠ (towerZero 7, towerZero 7))
    (rc1 rc2 : Tower128 × Tower128) (rest : List (Tower128 × Tower128))
    (x0 : Tower128 × Tower128) :
    0 < ((rcPairs (towerAll 7)).filter fun x => decide
      (spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB (rc1 :: rc2 :: rest)
          x (pairXor x δ) =
        spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB (rc1 :: rc2 :: rest)
          x0 (pairXor x0 δ))).length ∧
    ((rcPairs (towerAll 7)).filter fun x => decide
      (spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB (rc1 :: rc2 :: rest)
          x (pairXor x δ) =
        spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB (rc1 :: rc2 :: rest)
          x0 (pairXor x0 δ))).length ≤ 36 :=
  ⟨realized_trace_has_positive_count (rcPairs (towerAll 7))
      (fun x => spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB
        (rc1 :: rc2 :: rest) x (pairXor x δ)) x0
      (mem_rcPairs _ x0 (towerAll_complete 7 x0.1) (towerAll_complete 7 x0.2)),
    spn48_full_list_fixed_constants_trail_count δ hδ _ rc1 rc2 rest⟩


end Qsag
end


section
namespace Qsag
set_option autoImplicit false

/-! ## §1. Committed differentials: all trails summed -/

/-- Explicit inverse of the mixing layer `(u, v) ↦ (u + A v, v + B u)`. -/
def spnMixInv (mdsA mdsB : Tower128) (β : Tower128 × Tower128) : Tower128 × Tower128 :=
  let c := towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mdsA mdsB))
  (towerMul 7 c (towerAdd 7 β.1 (towerMul 7 mdsA β.2)),
   towerMul 7 c (towerAdd 7 β.2 (towerMul 7 mdsB β.1)))

private theorem mix_alg1 (A B x y : Tower128) :
    towerAdd 7 (towerAdd 7 x (towerMul 7 A y)) (towerMul 7 A (towerAdd 7 y (towerMul 7 B x))) =
      towerMul 7 (towerAdd 7 (towerOne 7) (towerMul 7 A B)) x := by
  rw [towerMul_add_distrib, ← towerMul_assoc, towerAdd_assoc,
    ← towerAdd_assoc 7 (towerMul 7 A y) (towerMul 7 A y), towerAdd_self_zero, towerZero_add,
    towerAdd_mul_distrib, towerOne_mul]

private theorem mix_alg2 (A B x y : Tower128) :
    towerAdd 7 (towerAdd 7 y (towerMul 7 B x)) (towerMul 7 B (towerAdd 7 x (towerMul 7 A y))) =
      towerMul 7 (towerAdd 7 (towerOne 7) (towerMul 7 A B)) y := by
  rw [towerMul_add_distrib, ← towerMul_assoc, towerAdd_assoc,
    ← towerAdd_assoc 7 (towerMul 7 B x) (towerMul 7 B x), towerAdd_self_zero, towerZero_add,
    towerAdd_mul_distrib, towerOne_mul, towerMul_comm 7 B A]

private theorem mix_det_inv (mds : ValidSpnMdsPair 7) (x : Tower128) :
    towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
      (towerMul 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)) x) = x := by
  have hD : towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB) ≠ towerZero 7 := fun h =>
    mds.hAB_ne_one ((tadd_eq_zero_iff _ _).mp h).symm
  rw [← towerMul_assoc, towerMul_comm 7 (towerInv 7 _), towerMul_inv 7 _ hD, towerOne_mul]

/-- The mixing layer hits `β` exactly at `spnMixInv β`. -/
theorem spnLinearMix_eq_iff (mds : ValidSpnMdsPair 7) (σ β : Tower128 × Tower128) :
    spnLinearMix 7 mds.mdsA mds.mdsB σ = β ↔ σ = spnMixInv mds.mdsA mds.mdsB β := by
  constructor
  · intro h
    rcases σ with ⟨u, v⟩
    subst h
    apply Prod.ext
    · show u = towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
        (towerAdd 7 (towerAdd 7 u (towerMul 7 mds.mdsA v))
          (towerMul 7 mds.mdsA (towerAdd 7 v (towerMul 7 mds.mdsB u))))
      rw [mix_alg1, mix_det_inv]
    · show v = towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
        (towerAdd 7 (towerAdd 7 v (towerMul 7 mds.mdsB u))
          (towerMul 7 mds.mdsB (towerAdd 7 u (towerMul 7 mds.mdsA v))))
      rw [mix_alg2, mix_det_inv]
  · intro h
    rcases β with ⟨p, q⟩
    subst h
    apply Prod.ext
    · show towerAdd 7
          (towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
            (towerAdd 7 p (towerMul 7 mds.mdsA q)))
          (towerMul 7 mds.mdsA
            (towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
              (towerAdd 7 q (towerMul 7 mds.mdsB p)))) = p
      rw [towerMul_left_comm_of_assoc 7 (towerMul_assoc 7) mds.mdsA, ← towerMul_add_distrib,
        mix_alg1, mix_det_inv]
    · show towerAdd 7
          (towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
            (towerAdd 7 q (towerMul 7 mds.mdsB p)))
          (towerMul 7 mds.mdsB
            (towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
              (towerAdd 7 p (towerMul 7 mds.mdsA q)))) = q
      rw [towerMul_left_comm_of_assoc 7 (towerMul_assoc 7) mds.mdsB, ← towerMul_add_distrib,
        mix_alg2, mix_det_inv]

/-- Number of constant lists of length `n` under which the committed pair ends with state
    difference `β`. Every trail leading to `β` is counted: this is the differential. -/
def spnFinalDiffCount (keys : List Tower128) (mdsA mdsB : Tower128) (n : Nat)
    (s s' β : Tower128 × Tower128) : Nat :=
  ((freshInputAssignments (rcPairs keys) n).filter fun ks =>
    decide (pairXor (spnRunList mdsA mdsB ks s) (spnRunList mdsA mdsB ks s') = β)).length

theorem spnFinalDiffCount_succ (keys : List Tower128) (mdsA mdsB : Tower128) (n : Nat)
    (s s' β : Tower128 × Tower128) :
    spnFinalDiffCount keys mdsA mdsB (n + 1) s s' β =
      rcSum (fun rc => spnFinalDiffCount keys mdsA mdsB n
        (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s') β) (rcPairs keys) := by
  unfold spnFinalDiffCount
  rw [freshInputAssignments, filter_prefixAssignments_length]
  rfl

/-- One round, exact: the differential count is a product of two lane counts at the unique
    S-box output difference that the mixing layer sends to `β`. -/
theorem spnFinalDiffCount_one (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (t t' β : Tower128 × Tower128) :
    spnFinalDiffCount keys mds.mdsA mds.mdsB 1 t t' β =
      laneCount keys t.1 t'.1 (spnMixInv mds.mdsA mds.mdsB β).1 *
        laneCount keys t.2 t'.2 (spnMixInv mds.mdsA mds.mdsB β).2 := by
  rw [spnFinalDiffCount_succ, ← sboxPairDiff_count]
  have hTerm : (fun rc => spnFinalDiffCount keys mds.mdsA mds.mdsB 0
      (spnRound128 mds.mdsA mds.mdsB rc t) (spnRound128 mds.mdsA mds.mdsB rc t') β) =
      fun rc => if decide (sboxPairDiff rc t t' = spnMixInv mds.mdsA mds.mdsB β) then 1 else 0 := by
    funext rc
    unfold spnFinalDiffCount
    refine (filter_singleton_length _ []).trans ?_
    show (if decide (pairXor (spnRound128 mds.mdsA mds.mdsB rc t)
        (spnRound128 mds.mdsA mds.mdsB rc t') = β) = true then 1 else 0) = _
    by_cases h : sboxPairDiff rc t t' = spnMixInv mds.mdsA mds.mdsB β
    · have hβ : pairXor (spnRound128 mds.mdsA mds.mdsB rc t)
          (spnRound128 mds.mdsA mds.mdsB rc t') = β := by
        rw [spnRound128_diff]; exact (spnLinearMix_eq_iff mds _ _).mpr h
      rw [ite_eq_left (decide_eq_true h), ite_eq_left (decide_eq_true hβ)]
    · have hβ : ¬ pairXor (spnRound128 mds.mdsA mds.mdsB rc t)
          (spnRound128 mds.mdsA mds.mdsB rc t') = β := fun hb =>
        h ((spnLinearMix_eq_iff mds _ _).mp (by rw [← spnRound128_diff]; exact hb))
      rw [ite_eq_right (fun hd => h (of_decide_eq_true hd)),
        ite_eq_right (fun hd => hβ (of_decide_eq_true hd))]
  rw [hTerm, rcSum_ite, Nat.mul_one]

/-- For a committed pair `s ≠ s'` and a nonzero multiplier `c`, at most `6·N` first-round
    constants make the second lane's S-box difference equal `c` times the first lane's. These
    are the constants after which one lane of the next round is inactive. -/
theorem lane_collapse_count_le (keys : List Tower128) (hNd : keys.Nodup)
    (c : Tower128) (hc : c ≠ towerZero 7) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    ((rcPairs keys).filter fun rc => decide
      (sboxLaneDiff rc.2 s.2 s'.2 = towerMul 7 c (sboxLaneDiff rc.1 s.1 s'.1))).length ≤
      keys.length * 6 := by
  rw [filter_rcPairs_length]
  apply rcSum_le_const
  intro a _
  show laneCount keys s.2 s'.2 (towerMul 7 c (sboxLaneDiff a s.1 s'.1)) ≤ 6
  apply laneCount_le_six keys hNd
  by_cases h2 : s.2 = s'.2
  · left
    intro hZero
    have h1 : s.1 = s'.1 := (sboxLaneDiff_eq_zero_iff a s.1 s'.1).mp
      (((towerMul_eq_zero_iff 7 _ _).mp hZero).resolve_left hc)
    exact hNe (Prod.ext h1 h2)
  · exact Or.inr h2

private theorem mix_snd_eq_iff (B x1 x2 y1 y2 : Tower128) :
    towerAdd 7 x2 (towerMul 7 B x1) = towerAdd 7 y2 (towerMul 7 B y1) ↔
      towerAdd 7 x2 y2 = towerMul 7 B (towerAdd 7 x1 y1) := by
  rw [tadd_cross_iff, towerMul_add_distrib]

/-- Second lanes agree after the round exactly on a `lane_collapse` event with `c = B`. -/
theorem spnRound128_snd_eq_count_le (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (hNd : keys.Nodup) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    ((rcPairs keys).filter fun rc => decide
      ((spnRound128 mds.mdsA mds.mdsB rc s).2 = (spnRound128 mds.mdsA mds.mdsB rc s').2)).length ≤
      keys.length * 6 := by
  refine Nat.le_trans (Nat.le_of_eq ?_)
    (lane_collapse_count_le keys hNd mds.mdsB mds.hB_ne_zero s s' hNe)
  apply congrArg List.length
  apply List.filter_congr
  intro rc _
  exact decide_eq_decide.mpr (mix_snd_eq_iff mds.mdsB _ _ _ _)

/-- First lanes agree after the round exactly on a `lane_collapse` event with `c = A⁻¹`. -/
theorem spnRound128_fst_eq_count_le (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (hNd : keys.Nodup) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    ((rcPairs keys).filter fun rc => decide
      ((spnRound128 mds.mdsA mds.mdsB rc s).1 = (spnRound128 mds.mdsA mds.mdsB rc s').1)).length ≤
      keys.length * 6 := by
  have hInv : towerMul 7 mds.mdsA (towerInv 7 mds.mdsA) = towerOne 7 :=
    towerMul_inv 7 _ mds.hA_ne_zero
  have hInvNe : towerInv 7 mds.mdsA ≠ towerZero 7 := fun h0 => by
    rw [h0, towerMul_zero] at hInv
    exact towerOne128_ne_zero hInv.symm
  refine Nat.le_trans (Nat.le_of_eq ?_)
    (lane_collapse_count_le keys hNd (towerInv 7 mds.mdsA) hInvNe s s' hNe)
  apply congrArg List.length
  apply List.filter_congr
  intro rc _
  apply decide_eq_decide.mpr
  show towerAdd 7 _ (towerMul 7 mds.mdsA _) = towerAdd 7 _ (towerMul 7 mds.mdsA _) ↔ _
  rw [tadd_cross_iff, ← towerMul_add_distrib]
  constructor
  · intro h
    show sboxLaneDiff rc.2 s.2 s'.2 = _
    have h2 := congrArg (towerMul 7 (towerInv 7 mds.mdsA)) h
    rw [← towerMul_assoc, towerMul_comm 7 (towerInv 7 mds.mdsA) mds.mdsA, hInv,
      towerOne_mul] at h2
    exact h2.symm
  · intro h
    have h2 : sboxLaneDiff rc.2 s.2 s'.2 =
        towerMul 7 (towerInv 7 mds.mdsA) (sboxLaneDiff rc.1 s.1 s'.1) := h
    show sboxLaneDiff rc.1 s.1 s'.1 = towerMul 7 mds.mdsA (sboxLaneDiff rc.2 s.2 s'.2)
    rw [h2, ← towerMul_assoc, hInv, towerOne_mul]

/-- **Two rounds, committed differential.** For a committed pair `s ≠ s'` and any target
    difference `β`, at most `36·N²` of the `N⁴` two-round constant lists produce `β`: the
    probability of a differential, with every trail counted, is at most `(6/N)²`. The four
    cases are the activity pattern of the last S-box layer's required output difference. -/
theorem spn_two_round_differential_count_le (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (hNd : keys.Nodup) (s s' : Tower128 × Tower128) (hNe : s ≠ s') (β : Tower128 × Tower128) :
    spnFinalDiffCount keys mds.mdsA mds.mdsB 2 s s' β ≤ 36 * (keys.length * keys.length) := by
  rw [spnFinalDiffCount_succ]
  simp only [spnFinalDiffCount_one]
  generalize spnMixInv mds.mdsA mds.mdsB β = ν
  have hU : ∀ rc, spnRound128 mds.mdsA mds.mdsB rc s ≠ spnRound128 mds.mdsA mds.mdsB rc s' :=
    fun rc => spnRound128_ne mds rc s s' hNe
  by_cases h1 : ν.1 = towerZero 7 <;> by_cases h2 : ν.2 = towerZero 7
  · refine Nat.le_trans (rcSum_le_const _ 0 _ fun rc _ => ?_) (by rw [Nat.mul_zero]; exact Nat.zero_le _)
    rw [h1, h2]
    by_cases hA : (spnRound128 mds.mdsA mds.mdsB rc s).1 = (spnRound128 mds.mdsA mds.mdsB rc s').1
    · have hB : (spnRound128 mds.mdsA mds.mdsB rc s).2 ≠ (spnRound128 mds.mdsA mds.mdsB rc s').2 :=
        fun hB => hU rc (Prod.ext hA hB)
      rw [laneCount_zero_target keys _ _ hB, Nat.mul_zero]; exact Nat.le_refl 0
    · rw [laneCount_zero_target keys _ _ hA, Nat.zero_mul]; exact Nat.le_refl 0
  · have hTerm : ∀ rc ∈ rcPairs keys,
        laneCount keys (spnRound128 mds.mdsA mds.mdsB rc s).1
            (spnRound128 mds.mdsA mds.mdsB rc s').1 ν.1 *
          laneCount keys (spnRound128 mds.mdsA mds.mdsB rc s).2
            (spnRound128 mds.mdsA mds.mdsB rc s').2 ν.2 ≤
        if decide ((spnRound128 mds.mdsA mds.mdsB rc s).1 =
            (spnRound128 mds.mdsA mds.mdsB rc s').1) then keys.length * 6 else 0 := by
      intro rc _
      by_cases hA : (spnRound128 mds.mdsA mds.mdsB rc s).1 = (spnRound128 mds.mdsA mds.mdsB rc s').1
      · rw [ite_eq_left (decide_eq_true hA)]
        exact Nat.mul_le_mul (laneCount_le_length keys _ _ _)
          (laneCount_le_six keys hNd _ _ _ (Or.inl h2))
      · rw [ite_eq_right (fun hd => hA (of_decide_eq_true hd)), h1,
          laneCount_zero_target keys _ _ hA, Nat.zero_mul]
        exact Nat.le_refl 0
    refine Nat.le_trans (rcSum_le_of_le _ _ _ hTerm) ?_
    rw [rcSum_ite]
    refine Nat.le_trans (Nat.mul_le_mul_right _ (spnRound128_fst_eq_count_le mds keys hNd s s' hNe)) ?_
    rw [Nat.mul_mul_mul_comm, Nat.mul_comm]
    exact Nat.le_refl _
  · have hTerm : ∀ rc ∈ rcPairs keys,
        laneCount keys (spnRound128 mds.mdsA mds.mdsB rc s).1
            (spnRound128 mds.mdsA mds.mdsB rc s').1 ν.1 *
          laneCount keys (spnRound128 mds.mdsA mds.mdsB rc s).2
            (spnRound128 mds.mdsA mds.mdsB rc s').2 ν.2 ≤
        if decide ((spnRound128 mds.mdsA mds.mdsB rc s).2 =
            (spnRound128 mds.mdsA mds.mdsB rc s').2) then keys.length * 6 else 0 := by
      intro rc _
      by_cases hB : (spnRound128 mds.mdsA mds.mdsB rc s).2 = (spnRound128 mds.mdsA mds.mdsB rc s').2
      · rw [ite_eq_left (decide_eq_true hB), Nat.mul_comm]
        exact Nat.mul_le_mul (laneCount_le_length keys _ _ _)
          (laneCount_le_six keys hNd _ _ _ (Or.inl h1))
      · rw [ite_eq_right (fun hd => hB (of_decide_eq_true hd)), h2,
          laneCount_zero_target keys _ _ hB, Nat.mul_zero]
        exact Nat.le_refl 0
    refine Nat.le_trans (rcSum_le_of_le _ _ _ hTerm) ?_
    rw [rcSum_ite]
    refine Nat.le_trans (Nat.mul_le_mul_right _ (spnRound128_snd_eq_count_le mds keys hNd s s' hNe)) ?_
    rw [Nat.mul_mul_mul_comm, Nat.mul_comm]
    exact Nat.le_refl _
  · refine Nat.le_trans (rcSum_le_const _ (6 * 6) _ fun rc _ =>
      Nat.mul_le_mul (laneCount_le_six keys hNd _ _ _ (Or.inl h1))
        (laneCount_le_six keys hNd _ _ _ (Or.inl h2))) ?_
    rw [rcPairs_length, Nat.mul_comm]
    exact Nat.le_refl _

/-- **Any number of rounds `≥ 2`, committed differential.** Earlier rounds only average the
    two-round bound over the states they reach, which stay distinct. -/
theorem spn_differential_count_le (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (hNd : keys.Nodup) (β : Tower128 × Tower128) :
    ∀ (n : Nat) (s s' : Tower128 × Tower128), s ≠ s' →
      spnFinalDiffCount keys mds.mdsA mds.mdsB (n + 2) s s' β ≤
        36 * (keys.length * keys.length) * (keys.length * keys.length) ^ n
  | 0, s, s', hNe => by
    rw [Nat.pow_zero, Nat.mul_one]
    exact spn_two_round_differential_count_le mds keys hNd s s' hNe β
  | n + 1, s, s', hNe => by
    rw [spnFinalDiffCount_succ]
    refine Nat.le_trans (rcSum_le_const _ _ _ fun rc _ =>
      spn_differential_count_le mds keys hNd β n _ _ (spnRound128_ne mds rc s s' hNe)) ?_
    rw [rcPairs_length, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm (keys.length * keys.length),
      Nat.mul_assoc]
    exact Nat.le_refl _

/-! ## §2. Davies–Meyer: the committed-pair collision game, and what invertibility gives -/

/-- Number of 48-round constant lists under which the committed pair collides in the actual
    `spnDaviesMeyer48` (permutation output xor input, as in Rust `algebraic_step_plain`). -/
def spnDmCollisionCount (keys : List Tower128) (mdsA mdsB : Tower128)
    (s s' : Tower128 × Tower128) : Nat :=
  ((freshInputAssignments (rcPairs keys) spnRounds).filter fun ks =>
    decide (spnDaviesMeyer48 mdsA mdsB (rcSchedule ks) s =
      spnDaviesMeyer48 mdsA mdsB (rcSchedule ks) s')).length

/-- **Committed-pair collision bound.** A Davies–Meyer collision of `s ≠ s'` is the
    differential `s ⊕ s' → s ⊕ s'` of the permutation, so at most a `36/N²` fraction of the
    constant lists make a committed pair collide. Scope: the pair is fixed before the
    constants are drawn. Nothing is claimed about finding a colliding pair for given constants. -/
theorem spn48_davies_meyer_committed_pair_collision_count_le (mds : ValidSpnMdsPair 7)
    (keys : List Tower128) (hNd : keys.Nodup) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    spnDmCollisionCount keys mds.mdsA mds.mdsB s s' ≤
      36 * (keys.length * keys.length) * (keys.length * keys.length) ^ 46 := by
  refine Nat.le_trans (Nat.le_of_eq ?_)
    (spn_differential_count_le mds keys hNd (pairXor s s') 46 s s' hNe)
  unfold spnDmCollisionCount spnFinalDiffCount
  apply congrArg List.length
  apply List.filter_congr
  intro ks hks
  have hLen : ks.length = spnRounds := mem_freshInputAssignments_length _ _ _ hks
  apply decide_eq_decide.mpr
  unfold spnDaviesMeyer48
  rw [← hLen, ← spnRunList_eq_iter, ← spnRunList_eq_iter]
  show (towerAdd 7 _ s.1, towerAdd 7 _ s.2) = (towerAdd 7 _ s'.1, towerAdd 7 _ s'.2) ↔
    (towerAdd 7 _ _, towerAdd 7 _ _) = (towerAdd 7 s.1 s'.1, towerAdd 7 s.2 s'.2)
  rw [Prod.mk.injEq, Prod.mk.injEq, tadd_cross_iff, tadd_cross_iff _ s.2]

/-- The committed-pair collision probability over `2^128` lane constants is below `2^-250`. -/
theorem spn48_davies_meyer_committed_pair_collision_atLeast_250_bits
    (mds : ValidSpnMdsPair 7) (keys : List Tower128) (hNd : keys.Nodup)
    (hN : keys.length = 2 ^ 128) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    atLeastBits 250 ⟨spnDmCollisionCount keys mds.mdsA mds.mdsB s s',
      (2 ^ 128 * 2 ^ 128) ^ 48,
      Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128))⟩ := by
  have h := spn48_davies_meyer_committed_pair_collision_count_le mds keys hNd s s' hNe
  rw [hN] at h
  show spnDmCollisionCount keys mds.mdsA mds.mdsB s s' * 2 ^ 250 ≤ (2 ^ 128 * 2 ^ 128) ^ 48
  refine Nat.le_trans (Nat.mul_le_mul_right _ h) ?_
  rw [show (2 ^ 128 * 2 ^ 128 : Nat) ^ 48 = (2 ^ 128 * 2 ^ 128) ^ 46 * (2 ^ 128 * 2 ^ 128) ^ 2 from
    Nat.pow_add _ 46 2, Nat.mul_right_comm]
  rw [Nat.mul_comm (36 * (2 ^ 128 * 2 ^ 128) * 2 ^ 250)]
  exact Nat.mul_le_mul_left _ (by decide)


end Qsag
end


section
namespace Qsag
set_option autoImplicit false

/-! ## §1. Integer sums over lists -/

/-- The character value `(-1)^b`. -/
def wsgn (b : Bool) : Int := if b then -1 else 1

theorem wsgn_xor (a b : Bool) : wsgn (a ^^ b) = wsgn a * wsgn b := by
  cases a <;> cases b <;> rfl

theorem wsgn_mul_self (a : Bool) : wsgn a * wsgn a = 1 := by cases a <;> rfl

/-- Sum of an integer-valued function over a list. -/
def isum {α : Type} (f : α → Int) : List α → Int
  | [] => 0
  | x :: xs => f x + isum f xs

theorem isum_congr {α : Type} (f g : α → Int) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → isum f l = isum g l
  | [], _ => rfl
  | x :: xs, h => by
    show f x + isum f xs = g x + isum g xs
    rw [h x List.mem_cons_self, isum_congr f g xs fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem isum_eq_zero {α : Type} (f : α → Int) :
    ∀ l : List α, (∀ x ∈ l, f x = 0) → isum f l = 0
  | [], _ => rfl
  | x :: xs, h => by
    show f x + isum f xs = 0
    rw [h x List.mem_cons_self, isum_eq_zero f xs fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem isum_add {α : Type} (f g : α → Int) :
    ∀ l : List α, isum (fun x => f x + g x) l = isum f l + isum g l
  | [] => rfl
  | x :: xs => by
    show f x + g x + isum (fun x => f x + g x) xs = f x + isum f xs + (g x + isum g xs)
    rw [isum_add f g xs, Int.add_assoc, Int.add_assoc, Int.add_left_comm (g x)]

theorem isum_mul_left {α : Type} (c : Int) (f : α → Int) :
    ∀ l : List α, isum (fun x => c * f x) l = c * isum f l
  | [] => (Int.mul_zero c).symm
  | x :: xs => by
    show c * f x + isum (fun x => c * f x) xs = c * (f x + isum f xs)
    rw [isum_mul_left c f xs, Int.mul_add]

theorem isum_mul_right {α : Type} (c : Int) (f : α → Int) :
    ∀ l : List α, isum (fun x => f x * c) l = isum f l * c
  | [] => (Int.zero_mul c).symm
  | x :: xs => by
    show f x * c + isum (fun x => f x * c) xs = (f x + isum f xs) * c
    rw [isum_mul_right c f xs, Int.add_mul]

theorem isum_swap {α β : Type} (F : α → β → Int) (l2 : List β) :
    ∀ l1 : List α, isum (fun x => isum (fun y => F x y) l2) l1 =
      isum (fun y => isum (fun x => F x y) l1) l2
  | [] => (isum_eq_zero _ l2 fun _ _ => rfl).symm
  | x :: xs => by
    show isum (fun y => F x y) l2 + isum (fun x => isum (fun y => F x y) l2) xs = _
    rw [isum_swap F l2 xs, ← isum_add]
    rfl

theorem isum_mul_isum {α β : Type} (A : α → Int) (B : β → Int) (l1 : List α) (l2 : List β) :
    isum A l1 * isum B l2 = isum (fun x => isum (fun y => A y * B x) l1) l2 := by
  rw [← isum_mul_left]
  exact isum_congr _ _ l2 fun x _ => (isum_mul_right (B x) A l1).symm

/-- A sum against the indicator of one listed point picks out that point's term. -/
theorem isum_indicator {α : Type} [DecidableEq α] (F : α → Int) (c : α) :
    ∀ l : List α, l.Nodup → c ∈ l → isum (fun y => if y = c then F y else 0) l = F c
  | [], _, h => absurd h List.not_mem_nil
  | y :: ys, hNd, hMem => by
    have hy := List.nodup_cons.mp hNd
    show (if y = c then F y else 0) + isum (fun y => if y = c then F y else 0) ys = F c
    by_cases hc : y = c
    · have hRest : isum (fun y => if y = c then F y else 0) ys = 0 :=
        isum_eq_zero _ ys fun z hz => ite_eq_right fun (hzc : z = c) =>
          hy.1 ((Eq.trans hzc hc.symm) ▸ hz)
      rw [ite_eq_left hc, hRest, hc, Int.add_zero]
    · have hIn : c ∈ ys := (List.mem_cons.mp hMem).resolve_left fun h => hc h.symm
      rw [ite_eq_right hc, isum_indicator F c ys hy.2 hIn, Int.zero_add]

theorem isum_const {α : Type} (c : Int) :
    ∀ l : List α, isum (fun _ => c) l = (l.length : Int) * c
  | [] => (Int.zero_mul c).symm
  | x :: xs => by
    show c + isum (fun _ => c) xs = ((xs.length + 1 : Nat) : Int) * c
    rw [isum_const c xs, Int.natCast_succ, Int.add_mul, Int.one_mul, Int.add_comm]

theorem isum_le {α : Type} (f g : α → Int) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ g x) → isum f l ≤ isum g l
  | [], _ => Int.le_refl 0
  | x :: xs, h =>
    Int.add_le_add (h x List.mem_cons_self)
      (isum_le f g xs fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem isum_append {α : Type} (f : α → Int) (l2 : List α) :
    ∀ l1 : List α, isum f (l1 ++ l2) = isum f l1 + isum f l2
  | [] => (Int.zero_add _).symm
  | x :: xs => by
    show f x + isum f (xs ++ l2) = f x + isum f xs + isum f l2
    rw [isum_append f l2 xs, Int.add_assoc]

theorem isum_map {α β : Type} (f : β → Int) (g : α → β) :
    ∀ l : List α, isum f (l.map g) = isum (fun x => f (g x)) l
  | [] => rfl
  | x :: xs => by
    show f (g x) + isum f (xs.map g) = f (g x) + isum (fun x => f (g x)) xs
    rw [isum_map f g xs]

theorem isum_pairList {α : Type} (F : α × α → Int) (l2 : List α) :
    ∀ l1 : List α, isum F (l1.flatMap fun a => l2.map fun b => (a, b)) =
      isum (fun a => isum (fun b => F (a, b)) l2) l1
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, isum_append, isum_map, isum_pairList F l2 xs]
    rfl

theorem int_mul_rearr (a s1 s2 b : Int) : (a * s1) * (s2 * b) = (a * b) * (s1 * s2) := by
  rw [Int.mul_assoc, Int.mul_assoc a b, ← Int.mul_assoc s1 s2 b, Int.mul_comm (s1 * s2) b]

theorem int_mul_rearr2 (a s1 b s2 : Int) : (a * s1) * (b * s2) = (a * b) * (s1 * s2) := by
  rw [Int.mul_assoc, Int.mul_left_comm s1 b s2, ← Int.mul_assoc]

/-! ## §2. Walsh coefficients, composition and the trail expansion -/

/-- A finite set of masks/points with a symmetric bilinear `Bool` pairing whose characters
    are orthogonal. `add` is the group law the pairing is linear in. -/
structure WalshSpace (α : Type) [DecidableEq α] where
  elems : List α
  dot : α → α → Bool
  add : α → α → α
  nodup : elems.Nodup
  complete : ∀ x : α, x ∈ elems
  dot_symm : ∀ a b : α, dot a b = dot b a
  dot_add : ∀ u a b : α, dot u (add a b) = (dot u a ^^ dot u b)
  orth : ∀ y y' : α, isum (fun v => wsgn (dot v y) * wsgn (dot v y')) elems =
    if y = y' then (elems.length : Int) else 0

/-- Unnormalized Walsh coefficient `Σ_x (-1)^(u·f(x) + w·x)`; the correlation of the output
    mask `u` with the input mask `w` is this divided by the number of points. -/
def walsh {α : Type} [DecidableEq α] (W : WalshSpace α) (f : α → α) (u w : α) : Int :=
  isum (fun x => wsgn (W.dot u (f x)) * wsgn (W.dot w x)) W.elems

/-- **Composition.** Summing the products of coefficients over the intermediate mask gives
    `N` times the coefficient of the composition. No probability is involved. -/
theorem walsh_comp {α : Type} [DecidableEq α] (W : WalshSpace α) (f g : α → α) (u w : α) :
    isum (fun v => walsh W g u v * walsh W f v w) W.elems =
      (W.elems.length : Int) * walsh W (fun x => g (f x)) u w := by
  have h1 : isum (fun v => walsh W g u v * walsh W f v w) W.elems =
      isum (fun v => isum (fun x => isum (fun y =>
        (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
          (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems) W.elems) W.elems :=
    isum_congr _ _ _ fun v _ => isum_mul_isum _ _ _ _
  have h2 := isum_swap (fun v x => isum (fun y =>
      (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
        (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems) W.elems W.elems
  have h3 : isum (fun x => isum (fun v => isum (fun y =>
        (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
          (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems) W.elems) W.elems =
      isum (fun x => (wsgn (W.dot u (g (f x))) * wsgn (W.dot w x)) *
        (W.elems.length : Int)) W.elems := by
    apply isum_congr
    intro x _
    rw [isum_swap (fun v y => (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
      (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems W.elems]
    have hInner : isum (fun y => isum (fun v =>
          (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
            (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems) W.elems =
        isum (fun y => if y = f x then
          (wsgn (W.dot u (g y)) * wsgn (W.dot w x)) * (W.elems.length : Int) else 0) W.elems := by
      apply isum_congr
      intro y _
      have hO := W.orth y (f x)
      have hT : isum (fun v => (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
            (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems =
          (wsgn (W.dot u (g y)) * wsgn (W.dot w x)) *
            isum (fun v => wsgn (W.dot v y) * wsgn (W.dot v (f x))) W.elems := by
        rw [← isum_mul_left]
        exact isum_congr _ _ _ fun v _ => int_mul_rearr _ _ _ _
      rw [hT, hO]
      by_cases hy : y = f x
      · rw [ite_eq_left hy, ite_eq_left hy]
      · rw [ite_eq_right hy, ite_eq_right hy, Int.mul_zero]
    rw [hInner]
    exact isum_indicator (fun y => (wsgn (W.dot u (g y)) * wsgn (W.dot w x)) *
      (W.elems.length : Int)) (f x) W.elems W.nodup (W.complete (f x))
  rw [h1, h2, h3, isum_mul_right, Int.mul_comm]
  rfl

/-- The identity map has coefficient `N` on the diagonal and `0` elsewhere. -/
theorem walsh_id {α : Type} [DecidableEq α] (W : WalshSpace α) (u w : α) :
    walsh W (fun x => x) u w = if u = w then (W.elems.length : Int) else 0 := by
  rw [← W.orth u w]
  exact isum_congr _ _ _ fun x _ => by rw [W.dot_symm u x, W.dot_symm w x]

/-- Rounds applied in list order (head first). -/
def composeRounds {α : Type} : List (α → α) → α → α
  | [], x => x
  | f :: fs, x => composeRounds fs (f x)

/-- Sum over every sequence of intermediate masks (every linear trail) of the product of the
    one-round coefficients along it. -/
def walshTrailSum {α : Type} [DecidableEq α] (W : WalshSpace α) : List (α → α) → α → α → Int
  | [], u, w => if u = w then (W.elems.length : Int) else 0
  | f :: fs, u, w => isum (fun v => walshTrailSum W fs u v * walsh W f v w) W.elems

/-- **Linear hull = signed sum of trail contributions**, exactly, for any list of rounds. -/
theorem walshTrailSum_eq {α : Type} [DecidableEq α] (W : WalshSpace α) :
    ∀ (fs : List (α → α)) (u w : α),
      walshTrailSum W fs u w =
        (W.elems.length : Int) ^ fs.length * walsh W (composeRounds fs) u w
  | [], u, w => by
    show (if u = w then (W.elems.length : Int) else 0) = _
    rw [← walsh_id W u w, List.length_nil, Int.pow_zero, Int.one_mul]
    rfl
  | f :: fs, u, w => by
    show isum (fun v => walshTrailSum W fs u v * walsh W f v w) W.elems = _
    have hStep : isum (fun v => walshTrailSum W fs u v * walsh W f v w) W.elems =
        (W.elems.length : Int) ^ fs.length *
          isum (fun v => walsh W (composeRounds fs) u v * walsh W f v w) W.elems := by
      rw [← isum_mul_left]
      exact isum_congr _ _ _ fun v _ => by rw [walshTrailSum_eq W fs u v, Int.mul_assoc]
    rw [hStep, walsh_comp, ← Int.mul_assoc, List.length_cons, Int.pow_succ]
    rfl

/-- Adding a constant after a map multiplies the coefficient by a sign. -/
theorem walsh_output_translate {α : Type} [DecidableEq α] (W : WalshSpace α) (f : α → α)
    (k u w : α) :
    walsh W (fun x => W.add (f x) k) u w = wsgn (W.dot u k) * walsh W f u w := by
  unfold walsh
  rw [← isum_mul_left]
  apply isum_congr
  intro x _
  rw [W.dot_add, wsgn_xor, Int.mul_comm (wsgn (W.dot u (f x))), Int.mul_assoc]

/-- Adding a constant before a map multiplies the coefficient by a sign (of the input mask).
    Derived from `walsh_comp` and orthogonality; no reindexing of the sum is used. -/
theorem walsh_input_translate {α : Type} [DecidableEq α] (W : WalshSpace α) (f : α → α)
    (k u w : α) :
    walsh W (fun x => f (W.add x k)) u w = wsgn (W.dot w k) * walsh W f u w := by
  have hPos : (W.elems.length : Int) ≠ 0 := by
    cases hE : W.elems with
    | nil => exact absurd (hE ▸ W.complete k) List.not_mem_nil
    | cons x xs =>
      have hp : (0 : Int) < ((x :: xs).length : Int) := Int.natCast_pos.mpr (Nat.succ_pos _)
      exact fun h0 => Int.lt_irrefl 0 (h0 ▸ hp)
  have hShift : ∀ v : α, walsh W (fun x => W.add x k) v w =
      wsgn (W.dot v k) * (if v = w then (W.elems.length : Int) else 0) := by
    intro v
    have h := walsh_output_translate W (fun x => x) k v w
    rw [walsh_id] at h
    exact h
  have hC := walsh_comp W (fun x => W.add x k) f u w
  have hSum : isum (fun v => walsh W f u v * walsh W (fun x => W.add x k) v w) W.elems =
      walsh W f u w * (wsgn (W.dot w k) * (W.elems.length : Int)) := by
    have hI := isum_indicator (fun v => walsh W f u v * (wsgn (W.dot v k) * (W.elems.length : Int)))
      w W.elems W.nodup (W.complete w)
    rw [← hI]
    apply isum_congr
    intro v _
    rw [hShift v]
    by_cases hv : v = w
    · rw [ite_eq_left hv, ite_eq_left hv]
    · rw [ite_eq_right hv, ite_eq_right hv, Int.mul_zero, Int.mul_zero]
  rw [hSum] at hC
  apply Int.eq_of_mul_eq_mul_left hPos
  rw [← hC, Int.mul_left_comm, Int.mul_comm (walsh W f u w)]
  exact Int.mul_left_comm _ _ _

/-! ## §3. Parseval and the floor for uniform bounds -/

/-- **Parseval.** For every map and every output mask, the squared coefficients over all
    input masks sum to `N²`. -/
theorem walsh_parseval {α : Type} [DecidableEq α] (W : WalshSpace α) (f : α → α) (u : α) :
    isum (fun w => walsh W f u w * walsh W f u w) W.elems =
      (W.elems.length : Int) * (W.elems.length : Int) := by
  have h1 : isum (fun w => walsh W f u w * walsh W f u w) W.elems =
      isum (fun w => isum (fun x => isum (fun y =>
        (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
          (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems) W.elems) W.elems :=
    isum_congr _ _ _ fun w _ => isum_mul_isum _ _ _ _
  have h2 := isum_swap (fun w x => isum (fun y =>
      (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
        (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems) W.elems W.elems
  have h3 : isum (fun x => isum (fun w => isum (fun y =>
        (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
          (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems) W.elems) W.elems =
      isum (fun _ => (W.elems.length : Int)) W.elems := by
    apply isum_congr
    intro x _
    rw [isum_swap (fun w y => (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
      (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems W.elems]
    have hInner : isum (fun y => isum (fun w =>
          (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
            (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems) W.elems =
        isum (fun y => if y = x then
          (wsgn (W.dot u (f y)) * wsgn (W.dot u (f x))) * (W.elems.length : Int) else 0) W.elems := by
      apply isum_congr
      intro y _
      have hO := W.orth y x
      have hT : isum (fun w => (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
            (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems =
          (wsgn (W.dot u (f y)) * wsgn (W.dot u (f x))) *
            isum (fun w => wsgn (W.dot w y) * wsgn (W.dot w x)) W.elems := by
        rw [← isum_mul_left]
        exact isum_congr _ _ _ fun w _ => int_mul_rearr2 _ _ _ _
      rw [hT, hO]
      by_cases hy : y = x
      · rw [ite_eq_left hy, ite_eq_left hy]
      · rw [ite_eq_right hy, ite_eq_right hy, Int.mul_zero]
    rw [hInner, isum_indicator (fun y => (wsgn (W.dot u (f y)) * wsgn (W.dot u (f x))) *
      (W.elems.length : Int)) x W.elems W.nodup (W.complete x), wsgn_mul_self, Int.one_mul]
  rw [h1, h2, h3, isum_const]

/-- **Floor.** If `B` bounds the squared coefficient for every input mask, then `B ≥ N`:
    some input mask has squared correlation at least `1/N` with any given output mask. -/
theorem walsh_uniform_bound_ge_card {α : Type} [DecidableEq α] (W : WalshSpace α)
    (f : α → α) (u : α) (B : Int)
    (hB : ∀ w ∈ W.elems, walsh W f u w * walsh W f u w ≤ B) :
    (W.elems.length : Int) ≤ B := by
  have hPos : (0 : Int) < (W.elems.length : Int) := by
    cases hE : W.elems with
    | nil => exact absurd (hE ▸ W.complete u) List.not_mem_nil
    | cons x xs => exact Int.natCast_pos.mpr (Nat.succ_pos _)
  have hSum := isum_le _ (fun _ => B) W.elems hB
  rw [walsh_parseval, isum_const] at hSum
  exact Int.le_of_mul_le_mul_left hSum hPos

/-! ## §4. The bit pairing on the Wiedemann tower and the actual round function -/

/-- Coordinatewise inner product of tower elements (all `2^k` bit coordinates). -/
def towerDot : (k : Nat) → TowerElem k → TowerElem k → Bool
  | 0, a, b => a && b
  | k + 1, a, b => towerDot k a.1 b.1 ^^ towerDot k a.2 b.2

theorem towerDot_symm : ∀ (k : Nat) (a b : TowerElem k), towerDot k a b = towerDot k b a
  | 0, a, b => Bool.and_comm a b
  | k + 1, a, b => by
    show (towerDot k a.1 b.1 ^^ towerDot k a.2 b.2) = (towerDot k b.1 a.1 ^^ towerDot k b.2 a.2)
    rw [towerDot_symm k a.1 b.1, towerDot_symm k a.2 b.2]

theorem bxor_swap (p q r s : Bool) : ((p ^^ q) ^^ (r ^^ s)) = ((p ^^ r) ^^ (q ^^ s)) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem towerDot_add : ∀ (k : Nat) (u a b : TowerElem k),
    towerDot k u (towerAdd k a b) = (towerDot k u a ^^ towerDot k u b)
  | 0, u, a, b => by cases u <;> cases a <;> cases b <;> rfl
  | k + 1, u, a, b => by
    show (towerDot k u.1 (towerAdd k a.1 b.1) ^^ towerDot k u.2 (towerAdd k a.2 b.2)) =
      ((towerDot k u.1 a.1 ^^ towerDot k u.2 a.2) ^^ (towerDot k u.1 b.1 ^^ towerDot k u.2 b.2))
    rw [towerDot_add k u.1, towerDot_add k u.2, bxor_swap]

theorem towerDot_orth : ∀ (k : Nat) (y y' : TowerElem k),
    isum (fun v => wsgn (towerDot k v y) * wsgn (towerDot k v y')) (towerAll k) =
      if y = y' then ((towerAll k).length : Int) else 0
  | 0, y, y' => by cases y <;> cases y' <;> rfl
  | k + 1, y, y' => by
    show isum (fun v => wsgn (towerDot k v.1 y.1 ^^ towerDot k v.2 y.2) *
        wsgn (towerDot k v.1 y'.1 ^^ towerDot k v.2 y'.2)) (rcPairs (towerAll k)) =
      if y = y' then ((rcPairs (towerAll k)).length : Int) else 0
    have hSplit : isum (fun v => wsgn (towerDot k v.1 y.1 ^^ towerDot k v.2 y.2) *
        wsgn (towerDot k v.1 y'.1 ^^ towerDot k v.2 y'.2)) (rcPairs (towerAll k)) =
        isum (fun a => wsgn (towerDot k a y.1) * wsgn (towerDot k a y'.1)) (towerAll k) *
          isum (fun b => wsgn (towerDot k b y.2) * wsgn (towerDot k b y'.2)) (towerAll k) := by
      unfold rcPairs
      rw [isum_pairList, ← isum_mul_right]
      apply isum_congr
      intro a _
      rw [← isum_mul_left]
      apply isum_congr
      intro b _
      show wsgn (towerDot k a y.1 ^^ towerDot k b y.2) *
        wsgn (towerDot k a y'.1 ^^ towerDot k b y'.2) = _
      rw [wsgn_xor, wsgn_xor, int_mul_rearr2]
    rw [hSplit, towerDot_orth k y.1 y'.1, towerDot_orth k y.2 y'.2, rcPairs_length,
      Int.natCast_mul]
    by_cases h : y = y'
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right h]
      by_cases h1 : y.1 = y'.1
      · have h2 : ¬ y.2 = y'.2 := fun h2 => h (Prod.ext h1 h2)
        rw [ite_eq_right h2, Int.mul_zero]
      · rw [ite_eq_right h1, Int.zero_mul]

/-- The tower with its bit pairing is a `WalshSpace` (level 7: one lane; level 8: the
    256-bit two-lane state, since `TowerElem 8 = Tower128 × Tower128`). -/
def towerWalsh (k : Nat) : WalshSpace (TowerElem k) where
  elems := towerAll k
  dot := towerDot k
  add := towerAdd k
  nodup := towerAll_nodup k
  complete := towerAll_complete k
  dot_symm := towerDot_symm k
  dot_add := towerDot_add k
  orth := towerDot_orth k

/-- **Round constants change only signs.** The Walsh coefficient of the actual round with
    constant `rc` is the coefficient of the constant-free round times `(-1)^(w·rc)`. Hence
    every one-round coefficient, and every product of them along a trail, has a magnitude
    that does not depend on the public constants; the constants decide how trails cancel. -/
theorem spnRound128_walsh_constant_sign (mdsA mdsB : Tower128) (rc u w : TowerElem 8) :
    walsh (towerWalsh 8) (spnRound128 mdsA mdsB rc) u w =
      wsgn (towerDot 8 w rc) *
        walsh (towerWalsh 8) (spnRound128 mdsA mdsB (towerZero 7, towerZero 7)) u w := by
  refine Eq.trans ?_ (walsh_input_translate (towerWalsh 8)
    (spnRound128 mdsA mdsB (towerZero 7, towerZero 7)) rc u w)
  apply congrArg (fun f => walsh (towerWalsh 8) f u w)
  funext x
  show spnRound128 mdsA mdsB rc x =
    spnRound128 mdsA mdsB (towerZero 7, towerZero 7) (towerAdd 7 x.1 rc.1, towerAdd 7 x.2 rc.2)
  unfold spnRound128
  rw [towerAdd_zero, towerAdd_zero]

/-- The exact trail expansion for the actual rounds: for any constant list, the sum over all
    intermediate 256-bit mask sequences of the products of one-round coefficients is
    `N^rounds` times the coefficient of the composed permutation. -/
theorem spn_walsh_hull_expansion (mdsA mdsB : Tower128) (ks : List (TowerElem 8))
    (u w : TowerElem 8) :
    walshTrailSum (towerWalsh 8) (ks.map fun rc => spnRound128 mdsA mdsB rc) u w =
      ((towerWalsh 8).elems.length : Int) ^ ks.length *
        walsh (towerWalsh 8)
          (composeRounds (ks.map fun rc => spnRound128 mdsA mdsB rc)) u w := by
  exact (walshTrailSum_eq (towerWalsh 8) _ u w).trans
    (congrArg (fun n => ((towerWalsh 8).elems.length : Int) ^ n *
      walsh (towerWalsh 8) (composeRounds (ks.map fun rc => spnRound128 mdsA mdsB rc)) u w)
      (List.length_map _))

/-- `composeRounds` over the mapped constant list is the permutation `spnRunList`. -/
theorem composeRounds_spnRound128 (mdsA mdsB : Tower128) :
    ∀ (ks : List (Tower128 × Tower128)) (x : Tower128 × Tower128),
      composeRounds (ks.map fun rc => spnRound128 mdsA mdsB rc) x = spnRunList mdsA mdsB ks x
  | [], _ => rfl
  | rc :: rest, x => composeRounds_spnRound128 mdsA mdsB rest (spnRound128 mdsA mdsB rc x)

/-- **Parseval floor on the 256-bit state.** For every map of the two-lane state (in
    particular the 48-round permutation under any constants) and every output mask, a bound
    valid for all input masks on the squared Walsh coefficient is at least `2^256`. -/
theorem spn_state_walsh_uniform_bound_ge_2_256 (f : TowerElem 8 → TowerElem 8)
    (u : TowerElem 8) (B : Int)
    (hB : ∀ w : TowerElem 8, walsh (towerWalsh 8) f u w * walsh (towerWalsh 8) f u w ≤ B) :
    ((2 ^ 2 ^ 8 : Nat) : Int) ≤ B := by
  have h := walsh_uniform_bound_ge_card (towerWalsh 8) f u B fun w _ => hB w
  rw [show (towerWalsh 8).elems.length = 2 ^ 2 ^ 8 from towerAll_length 8] at h
  exact h

/-- A product of 72 per-box squared-correlation bounds `36/2^128` is below the `2^-256`
    Parseval floor of the 256-bit state. Such a product can bound one trail's contribution
    (given a per-box Walsh bound), never the hull for all masks. -/
theorem walsh_trail_product_below_parseval_floor : 36 ^ 72 * 2 ^ 256 < (2 ^ 128) ^ 72 := by
  decide


end Qsag
end


section
namespace Qsag
set_option autoImplicit false

/-- Public reversible primitive. Both directions are exposed to the adversary. -/
structure PublicPermutation (State : Type) where
  forward : State → State
  inverse : State → State
  inverse_forward : ∀ x, inverse (forward x) = x
  forward_inverse : ∀ x, forward (inverse x) = x

private theorem mix_twice_lane (k : Nat) (a b x y : TowerElem k) :
    towerAdd k (towerAdd k x (towerMul k a y))
      (towerMul k a (towerAdd k y (towerMul k b x))) =
    towerMul k (towerAdd k (towerOne k) (towerMul k a b)) x := by
  rw [towerMul_add_distrib, ← towerAdd_assoc,
    towerAdd_assoc k x, towerAdd_self_zero, towerAdd_zero,
    towerAdd_mul_distrib, towerOne_mul, towerMul_assoc]

private theorem det_ne_zero {k : Nat} (mds : ValidSpnMdsPair k) :
    towerAdd k (towerOne k) (towerMul k mds.mdsA mds.mdsB) ≠ towerZero k := by
  intro h
  have he := congrArg (towerAdd k (towerOne k)) h
  rw [towerAdd_cancel, towerAdd_zero] at he
  exact mds.hAB_ne_one he

/-- Inverse of the linear layer: apply M again, divide both lanes by 1+A*B. -/
def publicSpnMixInverse {k : Nat} (mds : ValidSpnMdsPair k)
    (st : TowerElem k × TowerElem k) : TowerElem k × TowerElem k :=
  let d := towerInv k (towerAdd k (towerOne k) (towerMul k mds.mdsA mds.mdsB))
  let z := spnLinearMix k mds.mdsA mds.mdsB st
  (towerMul k d z.1, towerMul k d z.2)

private theorem det_cancel {k : Nat} (mds : ValidSpnMdsPair k) (x : TowerElem k) :
    towerMul k (towerInv k (towerAdd k (towerOne k) (towerMul k mds.mdsA mds.mdsB)))
      (towerMul k (towerAdd k (towerOne k) (towerMul k mds.mdsA mds.mdsB)) x) = x := by
  rw [← towerMul_assoc, towerMul_comm k (towerInv k _),
    towerMul_inv k _ (det_ne_zero mds), towerOne_mul]

theorem publicSpnMixInverse_left {k : Nat} (mds : ValidSpnMdsPair k)
    (st : TowerElem k × TowerElem k) :
    publicSpnMixInverse mds (spnLinearMix k mds.mdsA mds.mdsB st) = st := by
  apply Prod.ext
  · change towerMul k _ (towerAdd k (towerAdd k st.1 (towerMul k mds.mdsA st.2))
      (towerMul k mds.mdsA (towerAdd k st.2 (towerMul k mds.mdsB st.1)))) = st.1
    rw [mix_twice_lane, det_cancel]
  · change towerMul k _ (towerAdd k (towerAdd k st.2 (towerMul k mds.mdsB st.1))
      (towerMul k mds.mdsB (towerAdd k st.1 (towerMul k mds.mdsA st.2)))) = st.2
    rw [mix_twice_lane, towerMul_comm k mds.mdsB mds.mdsA, det_cancel]

theorem publicSpnMixInverse_right {k : Nat} (mds : ValidSpnMdsPair k)
    (st : TowerElem k × TowerElem k) :
    spnLinearMix k mds.mdsA mds.mdsB (publicSpnMixInverse mds st) = st := by
  have h := publicSpnMixInverse_left mds st
  have commute : spnLinearMix k mds.mdsA mds.mdsB (publicSpnMixInverse mds st) =
      publicSpnMixInverse mds (spnLinearMix k mds.mdsA mds.mdsB st) := by
    dsimp only [spnLinearMix, publicSpnMixInverse]
    simp only [towerMul_add_distrib, towerAdd_mul_distrib, towerMul_assoc, towerMul_comm,
      towerMul_left_comm_of_assoc k (towerMul_assoc k)]
  exact commute.trans h

/-- Undo mixing, undo x^7, then undo public round-constant XOR. -/
def publicSpnRoundInverse (mds : ValidSpnMdsPair 7) (rc st : Tower128 × Tower128) :
    Tower128 × Tower128 :=
  let z := publicSpnMixInverse mds st
  (towerAdd 7 (towerSbox7Inv128 z.1) rc.1, towerAdd 7 (towerSbox7Inv128 z.2) rc.2)

theorem publicSpnRoundInverse_left (mds : ValidSpnMdsPair 7) (rc st : Tower128 × Tower128) :
    publicSpnRoundInverse mds rc (spnRound128 mds.mdsA mds.mdsB rc st) = st := by
  unfold spnRound128 publicSpnRoundInverse
  rw [publicSpnMixInverse_left]
  simp only [towerSbox7Inv128_left_inv, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]

theorem publicSpnRoundInverse_right (mds : ValidSpnMdsPair 7) (rc st : Tower128 × Tower128) :
    spnRound128 mds.mdsA mds.mdsB rc (publicSpnRoundInverse mds rc st) = st := by
  unfold spnRound128 publicSpnRoundInverse
  simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerSbox7Inv128_right_inv]
  exact publicSpnMixInverse_right mds st

/-- Generic reverse traversal keeps the recursion independent of field representation. -/
def publicReverseIter {State : Type} (inverseRound : Nat → State → State) : Nat → State → State
  | 0, st => st
  | n + 1, st => publicReverseIter inverseRound n (inverseRound n st)

/-- Rounds are undone in descending order. -/
def publicSpnIterInverse (mds : ValidSpnMdsPair 7) (rcs : Nat → Tower128 × Tower128) :=
  publicReverseIter (fun n => publicSpnRoundInverse mds (rcs n))

private theorem reverseIter_left {State : Type}
    (f g : Nat → State → State) (trace : Nat → State → State)
    (hzero : ∀ x, trace 0 x = x)
    (hstep : ∀ n x, trace (n + 1) x = f n (trace n x))
    (hleft : ∀ n x, g n (f n x) = x) (n : Nat) (x : State) :
    publicReverseIter g n (trace n x) = x := by
  induction n with
  | zero => exact hzero x
  | succ n ih =>
    rw [hstep, publicReverseIter, hleft]
    exact ih

private theorem reverseIter_right {State : Type}
    (f g : Nat → State → State) (trace : Nat → State → State)
    (hzero : ∀ x, trace 0 x = x)
    (hstep : ∀ n x, trace (n + 1) x = f n (trace n x))
    (hright : ∀ n x, f n (g n x) = x) (n : Nat) (x : State) :
    trace n (publicReverseIter g n x) = x := by
  induction n generalizing x with
  | zero => exact hzero x
  | succ n ih => rw [publicReverseIter, hstep, ih, hright]

theorem publicSpnIterInverse_left (mds : ValidSpnMdsPair 7) (rcs : Nat → Tower128 × Tower128)
    (n : Nat) (st : Tower128 × Tower128) :
    publicSpnIterInverse mds rcs n (spnIterRounds128 mds.mdsA mds.mdsB rcs n st) = st := by
  unfold publicSpnIterInverse
  exact reverseIter_left
    (fun i => spnRound128 mds.mdsA mds.mdsB (rcs i))
    (fun i => publicSpnRoundInverse mds (rcs i))
    (spnIterRounds128 mds.mdsA mds.mdsB rcs)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun i x => publicSpnRoundInverse_left mds (rcs i) x) n st

theorem publicSpnIterInverse_right (mds : ValidSpnMdsPair 7) (rcs : Nat → Tower128 × Tower128)
    (n : Nat) (st : Tower128 × Tower128) :
    spnIterRounds128 mds.mdsA mds.mdsB rcs n (publicSpnIterInverse mds rcs n st) = st := by
  unfold publicSpnIterInverse
  exact reverseIter_right
    (fun i => spnRound128 mds.mdsA mds.mdsB (rcs i))
    (fun i => publicSpnRoundInverse mds (rcs i))
    (spnIterRounds128 mds.mdsA mds.mdsB rcs)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun i x => publicSpnRoundInverse_right mds (rcs i) x) n st

/-- Concrete public inverse in Rust's polynomial basis; no secret input is required. -/
def rustPublicSpnInverse (rcs : Nat → BitVec 128 × BitVec 128)
    (st : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  psiTower128Pair (publicSpnIterInverse parallelSeededMdsPair
    (fun i => polyToTower128Pair (rcs i)) spnRounds (polyToTower128Pair st))

theorem rustPublicSpnInverse_left (rcs : Nat → BitVec 128 × BitVec 128)
    (st : BitVec 128 × BitVec 128) :
    rustPublicSpnInverse rcs (rustSpnIter rcs spnRounds st) = st := by
  rw [rustSpnIter_eq_tower]
  unfold rustPublicSpnInverse
  rw [polyToTower128Pair_psiTower128Pair]
  have h := publicSpnIterInverse_left parallelSeededMdsPair
    (fun i => polyToTower128Pair (rcs i)) spnRounds (polyToTower128Pair st)
  simp only [parallelSeededMdsPair] at h ⊢
  rw [h, psiTower128Pair_polyToTower128Pair]

theorem rustPublicSpnInverse_right (rcs : Nat → BitVec 128 × BitVec 128)
    (st : BitVec 128 × BitVec 128) :
    rustSpnIter rcs spnRounds (rustPublicSpnInverse rcs st) = st := by
  rw [rustSpnIter_eq_tower]
  unfold rustPublicSpnInverse
  rw [polyToTower128Pair_psiTower128Pair]
  have h := publicSpnIterInverse_right parallelSeededMdsPair
    (fun i => polyToTower128Pair (rcs i)) spnRounds (polyToTower128Pair st)
  simp only [parallelSeededMdsPair] at h ⊢
  rw [h, psiTower128Pair_polyToTower128Pair]

abbrev PublicSpnState := BitVec 128 × BitVec 128

def rustPublicSpn (rcs : Nat → PublicSpnState) : PublicPermutation PublicSpnState where
  forward := rustSpnIter rcs spnRounds
  inverse := rustPublicSpnInverse rcs
  inverse_forward := rustPublicSpnInverse_left rcs
  forward_inverse := rustPublicSpnInverse_right rcs

/-- Whole-state feed-forward, not a sponge and not a secret-key block cipher. -/
def publicSpnFeedForward (p : PublicPermutation PublicSpnState) (x : PublicSpnState) :
    PublicSpnState := ((p.forward x).1 ^^^ x.1, (p.forward x).2 ^^^ x.2)

theorem rustAlgebraicStep_eq_publicFeedForward (rcs : Nat → PublicSpnState)
    (x : PublicSpnState) :
    rustAlgebraicStep rcs x = publicSpnFeedForward (rustPublicSpn rcs) x := by
  simp only [rustAlgebraicStep, publicSpnFeedForward, rustPublicSpn]

/-- Native Rust integer ranges, so no extra natural-number framing alias is admitted. -/
structure PublicChainAddress where
  pkSeed : List UInt8
  pkSeed_length : pkSeed.length = 32
  epoch : Fin (2 ^ 32)
  chainIdx : Fin (2 ^ 16)
  step : UInt8

/-- The family is indexed by the DERIVED tweak. Different addresses need not produce
independent permutations, nor even different tweaks. cSHAKE remains an explicit parameter. -/
def publicChainPermutation
    (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8)
    (address : PublicChainAddress) : PublicPermutation PublicSpnState :=
  rustPublicSpn (rustSpnRoundConstants framedXof
    (rustDeriveChainTweak framedXof address.pkSeed address.epoch.val address.chainIdx.val address.step))

/-- Exact lane framing and full-output connection to the deployed chain transcription. -/
theorem rustParallelChainStep_eq_publicFeedForward
    (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8)
    (address : PublicChainAddress) (cur : List UInt8) :
    rustParallelChainStep framedXof address.pkSeed address.epoch.val address.chainIdx.val address.step cur =
      rustLanesToBytes32 (publicSpnFeedForward (publicChainPermutation framedXof address)
        (rustBytes32ToLanes cur)) := by
  simp only [rustParallelChainStep, publicSpnFeedForward, publicChainPermutation, rustPublicSpn, rustAlgebraicStep]

/-- Chain composition preserves the per-position public address. There is no implicit
fixed-permutation iteration: each step may derive different round constants. -/
def publicChainRun
    (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8) :
    List PublicChainAddress → PublicSpnState → PublicSpnState
  | [], x => x
  | address :: rest, x => publicChainRun framedXof rest
      (publicSpnFeedForward (publicChainPermutation framedXof address) x)

def rustPublicChainRun
    (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8) :
    List PublicChainAddress → List UInt8 → List UInt8
  | [], bytes => bytes
  | address :: rest, bytes => rustPublicChainRun framedXof rest
      (rustParallelChainStep framedXof address.pkSeed address.epoch.val address.chainIdx.val address.step bytes)

theorem publicChainRun_bytes
    (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8)
    (addresses : List PublicChainAddress) (x : PublicSpnState) :
    rustPublicChainRun framedXof addresses (rustLanesToBytes32 x) =
      rustLanesToBytes32 (publicChainRun framedXof addresses x) := by
  induction addresses generalizing x with
  | nil => rfl
  | cons address rest ih =>
    simp only [rustPublicChainRun, publicChainRun,
      rustParallelChainStep_eq_publicFeedForward, rustBytes32ToLanes_lanesToBytes32, ih]

/-- A public inverse query constructs a fixed point of this feed-forward mode. This is
NOT a chosen-target preimage attack and does not give a fixed point shared by chain steps. -/
theorem publicSpnFeedForward_fixedPoint (p : PublicPermutation PublicSpnState) :
    publicSpnFeedForward p (p.inverse (0#128, 0#128)) = p.inverse (0#128, 0#128) := by
  unfold publicSpnFeedForward
  rw [p.forward_inverse]
  simp only [BitVec.zero_xor]

theorem publicChain_fixedPoint_bytes
    (framedXof : List UInt8 → List (List UInt8) → Nat → List UInt8) (address : PublicChainAddress) :
    let node := rustLanesToBytes32 ((publicChainPermutation framedXof address).inverse (0#128, 0#128))
    rustParallelChainStep framedXof address.pkSeed address.epoch.val address.chainIdx.val address.step node = node := by
  dsimp only
  rw [rustParallelChainStep_eq_publicFeedForward, rustBytes32ToLanes_lanesToBytes32,
    publicSpnFeedForward_fixedPoint]

/-- Idealization requires sampling this type, with a stated distribution. A fixed member
is merely a permutation, and carries no pseudorandomness claim. -/
def identityPublicPermutation : PublicPermutation PublicSpnState where
  forward := id
  inverse := id
  inverse_forward := fun _ => rfl
  forward_inverse := fun _ => rfl

/-- Nonvacuity guard: the permutation laws alone cannot imply collision resistance
of the feed-forward construction. Distinct explicit 256-bit nodes collide. -/
theorem publicPermutation_laws_allow_feedForward_collision :
    (0#128, 0#128) ≠ (1#128, 0#128) ∧
    publicSpnFeedForward identityPublicPermutation (0#128, 0#128) =
      publicSpnFeedForward identityPublicPermutation (1#128, 0#128) := by
  constructor
  · intro h
    have h0 := congrArg Prod.fst h
    contradiction
  · decide

/-- Primitive access includes both public directions. This operational classical subgame
is also available to quantum adversaries, but does not purport to define quantum states. -/
inductive PublicPermutationDirection where
  | forward | inverse
  deriving DecidableEq

def publicPermutationQuery {State : Type} (p : PublicPermutation State)
    (direction : PublicPermutationDirection) (x : State) : State :=
  match direction with
  | .forward => p.forward x
  | .inverse => p.inverse x

/-- Adaptive terminating public-primitive programs. The continuation receives the actual
answer, not an assumed classically observable log of a coherent quantum query. -/
inductive PublicPermutationProgram (State Result : Type) where
  | done : Result → PublicPermutationProgram State Result
  | query : PublicPermutationDirection → State →
      (State → PublicPermutationProgram State Result) → PublicPermutationProgram State Result

/-- Result and separate forward/inverse query counts along the actual execution. -/
def runPublicPermutationProgram {State Result : Type} (p : PublicPermutation State) :
    PublicPermutationProgram State Result → Result × Nat × Nat
  | .done result => (result, 0, 0)
  | .query direction x next =>
      let answer := runPublicPermutationProgram p (next (publicPermutationQuery p direction x))
      match direction with
      | .forward => (answer.1, answer.2.1 + 1, answer.2.2)
      | .inverse => (answer.1, answer.2.1, answer.2.2 + 1)

def publicFixedPointAttack : PublicPermutationProgram PublicSpnState PublicSpnState :=
  .query .inverse (0#128, 0#128) (fun x => .done x)

theorem publicFixedPointAttack_one_inverse (p : PublicPermutation PublicSpnState) :
    runPublicPermutationProgram p publicFixedPointAttack = (p.inverse (0#128, 0#128), 0, 1) := by
  simp only [runPublicPermutationProgram, publicFixedPointAttack, publicPermutationQuery]

/-- Mode-specific fixed-point game, with primitive access charged in each direction.
Mode evaluation for checking the winning relation is one additional forward call.
This event holds for every permutation, hence for every distribution over permutations. -/
def publicFeedForwardFixedPointGame (p : PublicPermutation PublicSpnState)
    (attack : PublicPermutationProgram PublicSpnState PublicSpnState) : Prop :=
  let result := runPublicPermutationProgram p attack
  result.2.1 = 0 ∧ result.2.2 ≤ 1 ∧ publicSpnFeedForward p result.1 = result.1

theorem publicFixedPointAttack_wins (p : PublicPermutation PublicSpnState) :
    publicFeedForwardFixedPointGame p publicFixedPointAttack :=
  ⟨rfl, Nat.le_refl 1, publicSpnFeedForward_fixedPoint p⟩

/-- Separate fresh-image inversion event for the feed-forward mode. A fixed-point
witness is not an automatic winner here: the target depends on challenge x. -/
def publicFeedForwardPreimageGame (p : PublicPermutation PublicSpnState)
    (attack : PublicSpnState → PublicPermutationProgram PublicSpnState PublicSpnState)
    (challenge : PublicSpnState) (forwardBudget inverseBudget : Nat) : Prop :=
  let target := publicSpnFeedForward p challenge
  let result := runPublicPermutationProgram p (attack target)
  result.2.1 ≤ forwardBudget ∧ result.2.2 ≤ inverseBudget ∧
    publicSpnFeedForward p result.1 = target


end Qsag
end

public section
namespace Qsag
theorem polyToTower128_mds_constants :
    polyToTower128 gf128MdsAPolyBits = gf128MdsATower ∧
    polyToTower128 gf128MdsBPolyBits = gf128MdsBTower := by
  refine ⟨?_, ?_⟩
  · rw [← gf128_mds_constants_certified.1, polyToTower128_psiTower128ToPoly]
  · rw [← gf128_mds_constants_certified.2.1, polyToTower128_psiTower128ToPoly]

end Qsag
end

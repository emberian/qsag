module
public import Qsag.Protocol.Aggregation.ZkHemV2PackedFiberCerts
public import Qsag.Protocol.Aggregation.BinaryFoldAgreement
import Qsag.Math.Tactic.CommRing
import Qsag.Tactic.AssuranceKit

/-!
# Scalar WHIR folding on the quintic Goldilocks extension

The fold and coset-index theorems apply at variable arity. The deployed
parameter rows supply the geometry for the packed verifier. The unconditional
round-by-round proof in this module uses the 256-point, three-stage schedule
whose agreement thresholds lie within the unique-decoding radius.
-/

public section
namespace Qsag.SuccinctWhirAgg

open CommRingOps ClosedFs ClosedWhir ZkHemV2Packed ZkHemV2Cert

set_option exponentiation.threshold 100000
local notation "K" => QuinticGoldilocks
local infixl:65 " +ᵍ " => add
local infixl:65 " -ᵍ " => sub
local infixl:70 " *ᵍ " => mul

/-- Interpolate the even and odd evaluations on an antipodal pair. -/
def quinticWhirFold2 (x α fPos fNeg : K) : K :=
  (fPos +ᵍ fNeg) *ᵍ LawfulField.inv (one +ᵍ one) +ᵍ
    α *ᵍ (fPos -ᵍ fNeg) *ᵍ LawfulField.inv ((one +ᵍ one) *ᵍ x)

/-- Coefficients of the even polynomial plus α times the odd polynomial. -/
def foldPolyCoeffs (α : K) : List K → List K
  | [] => []
  | [a] => [a]
  | a :: b :: p => (a +ᵍ α *ᵍ b) :: foldPolyCoeffs α p

theorem foldPolyCoeffs_length (α : K) : ∀ P : List K,
    (foldPolyCoeffs α P).length = (P.length + 1) / 2
  | [] => rfl
  | [a] => by simp [foldPolyCoeffs]
  | a :: b :: rest => by
    simp only [foldPolyCoeffs, List.length_cons, foldPolyCoeffs_length α rest]; omega

private theorem eval_split (x : K) : ∀ (P : List K),
    ∃ e o : K, RoundPoly.evalCoeffs P x = e +ᵍ x *ᵍ o ∧
      RoundPoly.evalCoeffs P (neg x) = e -ᵍ x *ᵍ o ∧
      ∀ α, RoundPoly.evalCoeffs (foldPolyCoeffs α P) (x *ᵍ x) = e +ᵍ α *ᵍ o
  | [] => by
    refine ⟨zero, zero, ?_, ?_, fun α => ?_⟩ <;>
      simp only [foldPolyCoeffs, RoundPoly.evalCoeffs_nil] <;> constructive_ring
  | [a] => by
    refine ⟨a, zero, ?_, ?_, fun α => ?_⟩ <;>
      simp only [foldPolyCoeffs, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil] <;> constructive_ring
  | a :: b :: p => by
    obtain ⟨e, o, hp, hn, hf⟩ := eval_split x p
    refine ⟨a +ᵍ x *ᵍ x *ᵍ e, b +ᵍ x *ᵍ x *ᵍ o, ?_, ?_, fun α => ?_⟩ <;>
      simp only [foldPolyCoeffs, RoundPoly.evalCoeffs_cons, hp, hn, hf] <;> constructive_ring

theorem quinticWhirFold2_evalCoeffs (x α : K) (P : List K) (hx : x ≠ zero) :
    quinticWhirFold2 x α (RoundPoly.evalCoeffs P x) (RoundPoly.evalCoeffs P (neg x)) =
      RoundPoly.evalCoeffs (foldPolyCoeffs α P) (x *ᵍ x) := by
  obtain ⟨e, o, hp, hn, hf⟩ := eval_split x P
  let two : K := one +ᵍ one
  have ht : two ≠ zero := by decide +kernel
  have htx : two *ᵍ x ≠ zero := fun h =>
    (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).elim ht hx
  rw [quinticWhirFold2, hp, hn, hf]
  calc
    _ = e *ᵍ (two *ᵍ LawfulField.inv two) +ᵍ
        α *ᵍ o *ᵍ ((two *ᵍ x) *ᵍ LawfulField.inv (two *ᵍ x)) := by
      dsimp only [two]; constructive_ring
    _ = _ := by rw [LawfulField.mul_inv_cancel ht, LawfulField.mul_inv_cancel htx,
                    LawfulCommRing.mul_one, LawfulCommRing.mul_one]

/-- Binary exponentiation avoids materializing the entire subgroup for a query. -/
private def basePower (g : Goldilocks) (n : Nat) : Goldilocks :=
  if h : n = 0 then one else
    let z := basePower g (n / 2)
    if n % 2 = 0 then z *ᵍ z else g *ᵍ (z *ᵍ z)
termination_by n
decreasing_by omega

private theorem basePower_eq (g : Goldilocks) (n : Nat) : basePower g n = ZkHemV2.fpow g n := by
  rw [basePower]
  split
  · rename_i h; subst n; rw [ZkHemV2.fpow_zero]
  · rename_i h
    dsimp only
    rw [basePower_eq g (n / 2), ← ZkHemV2.fpow_add]
    split
    · congr 1; omega
    · conv => rhs; rw [show n = (n / 2 + n / 2) + 1 by omega, ZkHemV2.fpow_succ]
termination_by n
decreasing_by omega

def cosetPoint (k j : Nat) : K :=
  QuinticGoldilocks.ofBase (basePower (ZkHemV2.twoAdicElem k) j)

theorem cosetPoint_table (k : Nat) :
    (List.range (2 ^ k)).map (cosetPoint k) =
      (ZkHemV2.twoAdicCoset k).map QuinticGoldilocks.ofBase := by
  rw [ZkHemV2.twoAdicCoset_eq_map, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [cosetPoint, basePower_eq, Function.comp_def]

def fiberPoint (k : Nat) (x : K) (j : Nat) : K := x *ᵍ cosetPoint k j

theorem fiberPoint_antipode (k j : Nat) (hk : k + 1 ≤ 32) (x : K) :
    fiberPoint (k + 1) x (2 ^ k + j) = neg (fiberPoint (k + 1) x j) := by
  simp only [fiberPoint, cosetPoint, basePower_eq, ZkHemV2.fpow_add,
    ZkHemV2.twoAdicElem_half_pow k hk, QuinticGoldilocks.ofBase_mul, QuinticGoldilocks.ofBase_neg,
    QuinticGoldilocks.ofBase_one]
  constructive_ring

theorem fiberPoint_square (k j : Nat) (hk : k + 1 ≤ 32) (x : K) :
    fiberPoint (k + 1) x j *ᵍ fiberPoint (k + 1) x j = fiberPoint k (x *ᵍ x) j := by
  unfold fiberPoint cosetPoint
  rw [basePower_eq, basePower_eq, ← ZkHemV2.twoAdicElem_sq k hk, ZkHemV2.fpow_mul_base,
    QuinticGoldilocks.ofBase_mul]
  constructive_ring

private theorem root_stride (k : Nat) : ∀ s, k + s ≤ 32 →
    ZkHemV2.fpow (ZkHemV2.twoAdicElem (k+s)) (2^s) = ZkHemV2.twoAdicElem k
  | 0, _ => by simp only [Nat.add_zero, Nat.pow_zero, ZkHemV2.fpow_succ,
      ZkHemV2.fpow_zero, LawfulCommRing.mul_one]
  | s+1, h => by
    rw [Nat.pow_succ', Nat.two_mul, ZkHemV2.fpow_add, ← ZkHemV2.fpow_mul_base]
    change ZkHemV2.fpow (ZkHemV2.twoAdicElem ((k+s)+1) *ᵍ ZkHemV2.twoAdicElem ((k+s)+1))
      (2^s) = _
    rw [ZkHemV2.twoAdicElem_sq (k+s) (by omega), root_stride k s (by omega)]

private theorem power_stride (g : Goldilocks) (m : Nat) :
    ∀ j, ZkHemV2.fpow g (j*m) = ZkHemV2.fpow (ZkHemV2.fpow g m) j
  | 0 => by rw [Nat.zero_mul, ZkHemV2.fpow_zero, ZkHemV2.fpow_zero]
  | j+1 => by rw [Nat.succ_mul, Nat.add_comm, ZkHemV2.fpow_add, power_stride g m j, ZkHemV2.fpow_succ]

/-- Positions j+b·n read by stageQueries are the consecutive points of the
    order-2^k fiber based at j, even when different stages use different rates. -/
theorem cosetPoint_strided (k s j b : Nat) (h : k+s ≤ 32) :
    cosetPoint (k+s) (j+b*2^s) = fiberPoint k (cosetPoint (k+s) j) b := by
  simp only [fiberPoint, cosetPoint, basePower_eq, ZkHemV2.fpow_add, power_stride,
    root_stride k s h, QuinticGoldilocks.ofBase_mul]

private theorem cosetPoint_ne_zero (k j : Nat) (hk : k ≤ 32) : cosetPoint k j ≠ zero := by
  rw [cosetPoint, basePower_eq, ← QuinticGoldilocks.ofBase_zero]
  exact fun h => ZkHemV2.fpow_ne_zero (ZkHemV2.twoAdicElem_ne_zero k hk) j
    (QuinticGoldilocks.ofBase_injective h)

private theorem mul_nonzero {a b : K} (ha : a ≠ zero) (hb : b ≠ zero) : a *ᵍ b ≠ zero :=
  fun h => (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).elim ha hb

private theorem fiberPoint_ne_zero (k j : Nat) (hk : k ≤ 32) (x : K) (hx : x ≠ zero) :
    fiberPoint k x j ≠ zero := by
  apply mul_nonzero hx
  unfold cosetPoint
  rw [basePower_eq, ← QuinticGoldilocks.ofBase_zero]
  exact fun h => ZkHemV2.fpow_ne_zero (ZkHemV2.twoAdicElem_ne_zero k hk) j
    (QuinticGoldilocks.ofBase_injective h)

def fiberEvaluations (k : Nat) (x : K) (P : List K) : List K :=
  (List.range (2 ^ k)).map fun j => RoundPoly.evalCoeffs P (fiberPoint k x j)

private theorem fiberEvaluations_getD (k j : Nat) (x : K) (P : List K) (hj : j < 2 ^ k) :
    (fiberEvaluations k x P).getD j zero = RoundPoly.evalCoeffs P (fiberPoint k x j) := by
  unfold fiberEvaluations
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (List.length_range ▸ hj), List.getElem_range]
  rfl

/-- The whole queried fiber folds to the evaluation of the repeatedly folded coefficients. -/
theorem foldBlock_evalCoeffs (env : WhirEnv K) (he : env.fold2 = quinticWhirFold2)
    (hp : env.fiberPoint = some fiberPoint) (αs : List K) (x : K) (P : List K)
    (hk : αs.length ≤ 32) (hx : x ≠ zero) :
    foldBlock env αs x (fiberEvaluations αs.length x P) =
      RoundPoly.evalCoeffs (αs.foldl (fun p α => foldPolyCoeffs α p) P)
        (ZkHemV2.pow2Iter αs.length x) := by
  induction αs generalizing x P with
  | nil =>
    have b0 : basePower (ZkHemV2.twoAdicElem 0) 0 = one := by rw [basePower_eq, ZkHemV2.fpow_zero]
    simp only [foldBlock, fiberEvaluations, List.length_nil, Nat.pow_zero, List.range_one,
      List.map_cons, List.map_nil, List.headD_cons, List.foldl_nil, fiberPoint, cosetPoint,
      b0, QuinticGoldilocks.ofBase_one, LawfulCommRing.mul_one, ZkHemV2.pow2Iter_zero]
  | cons a rest ih =>
    have hlen : (fiberEvaluations (rest.length + 1) x P).length / 2 = 2 ^ rest.length := by
      rw [fiberEvaluations, List.length_map, List.length_range, Nat.pow_succ, Nat.mul_div_cancel]
      decide
    rw [foldBlock, hp, List.length_cons, hlen]
    have layer : (List.range (2 ^ rest.length)).map (fun j =>
        env.fold2 (fiberPoint (rest.length + 1) x j) a
          ((fiberEvaluations (rest.length + 1) x P).getD j zero)
          ((fiberEvaluations (rest.length + 1) x P).getD (2 ^ rest.length + j) zero)) =
        fiberEvaluations rest.length (x *ᵍ x) (foldPolyCoeffs a P) := by
      apply List.map_congr_left
      intro j hj
      have hj' := List.mem_range.mp hj
      rw [he, fiberEvaluations_getD _ _ _ _ (by rw [Nat.pow_succ]; omega),
        fiberEvaluations_getD _ _ _ _ (by rw [Nat.pow_succ]; omega),
        fiberPoint_antipode _ _ hk, quinticWhirFold2_evalCoeffs _ _ _ (fiberPoint_ne_zero (rest.length + 1) j hk x hx),
        fiberPoint_square _ _ hk]
    dsimp only
    rw [layer, ih _ _ (Nat.le_of_succ_le hk) (mul_nonzero hx hx), List.foldl_cons]
    congr 1
    simpa only [ZkHemV2.pow2Iter_one] using (ZkHemV2.pow2Iter_add rest.length 1 x).symm

theorem cosetPoint_folded (k s j : Nat) (h : k+s ≤ 32) :
    ZkHemV2.pow2Iter k (cosetPoint (k+s) j) = cosetPoint s j := by
  simp only [cosetPoint, basePower_eq, ZkHemV2.pow2Iter_eq_fpow, ZkHemV2.fpow_ofBase]
  rw [← power_stride, Nat.mul_comm (2^k) j, power_stride, Nat.add_comm k s,
    root_stride s k (by omega)]

theorem foldBlock_stageQueries (env : WhirEnv K) (he : env.fold2 = quinticWhirFold2)
    (hp : env.fiberPoint = some fiberPoint) (as : List K) (s j : Nat) (h : as.length+s ≤ 32)
    (P : List K) :
    foldBlock env as (cosetPoint (as.length+s) j) ((List.range (2^as.length)).map
      (fun b => RoundPoly.evalCoeffs P (cosetPoint (as.length+s) (j+b*2^s)))) =
    RoundPoly.evalCoeffs (as.foldl (fun p α => foldPolyCoeffs α p) P)
      (cosetPoint s j) := by
  rw [← cosetPoint_folded as.length s j h]
  simp only [cosetPoint_strided _ _ _ _ h]
  exact foldBlock_evalCoeffs env he hp as _ P (by omega) (cosetPoint_ne_zero _ _ h)

/-! ## Round challenge sampling -/

/-- Five disjoint 400-bit field squeezes, followed by 32-bit position draws.
    Fold and commit rounds use field slots from zero. On the answer round the
    combiner also uses a field slot, disjoint from every sampled position. -/
def whirField (c j : Nat) : K := decodeQuintic400 ((c >>> (400 * (j % 5))) % 2 ^ 400)

theorem whirField_first (c : Nat) : whirField c 0 = decodeQuintic400 (c % 2^400) := by
  simp [whirField]

def whirPosition (c j n : Nat) : Nat := ((c >>> (2000 + 32 * j)) % 2 ^ 32) % n

/-- A full transcript squeeze can select leaf one as its first query. -/
theorem whirPosition_reaches_second_leaf : whirPosition (2 ^ 2000) 0 2 = 1 := by decide +kernel

/-- A scalar 400-bit round supplies none of the bits used to choose positions in
    the packed verifier. Every such seed selects the same leaf in every query. -/
theorem scalar_digest_collapses_packed_positions (seed : BitVec 400) (j n : Nat) :
    whirPosition seed.toNat j n = 0 := by
  have h : 2 ^ 400 ≤ 2 ^ (2000 + 32 * j) := Nat.pow_le_pow_right (by decide) (by omega)
  simp [whirPosition, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le seed.isLt h)]

theorem tooth_scalar_digest_cannot_reach_second_leaf :
    ¬ ∃ seed : BitVec 400, whirPosition seed.toNat 0 2 = 1 := by
  rintro ⟨seed, hit⟩
  rw [scalar_digest_collapses_packed_positions] at hit
  contradiction

#tooth_pair whirPosition_reaches_second_leaf vs tooth_scalar_digest_cannot_reach_second_leaf

/-- Count full-width round seeds mapping into a list of exceptional fold challenges.
    The additive one accounts for the bias in reducing a 400-bit word modulo p^5. -/
theorem whirField_fold_bad_seeds (hi : Nat) (S : List K) :
    qsum (2^(hi+400)) (fun c => if S.any (fun z => decide (whirField c.val 0 = z))
      then 1 else 0) ≤ 2^hi * (S.length * (2^400 / quinticGoldilocksCard + 1)) := by
  let hit := fun t : K => if S.any (fun z => decide (t = z)) then 1 else 0
  have proj (c : Nat) : whirField c 0 = decodeQuintic400 (c % 2^400) := by simp [whirField]
  change qsum _ (fun c => hit (whirField c.val 0)) ≤ _
  apply Nat.le_trans (Nat.le_of_eq (qsum_mul_mod_eq (Nat.pow_add 2 hi 400) (Nat.two_pow_pos 400)
    (fun c => hit (whirField c.val 0)) (fun u => hit (decodeQuintic400 u))
    (fun c => congrArg hit (proj c.val))))
  apply Nat.mul_le_mul_left
  apply qsum_any_le_mul _ _ (fun z i => decide (decodeQuintic400 i.val = z))
  intro z _
  simpa only [decide_eq_true_eq] using decodeQuintic400_preimage_le (2^400) z

/-- Transfer a bound on distinct bad field elements into the full-width fold seed space. -/
theorem whirField_predicate_mass (hi B : Nat) (bad : K → Bool)
    (hc : ∀ S : List K, S.Nodup → (∀ t ∈ S, bad t = true) → S.length ≤ B) :
    qsum (2^(hi+400)) (fun c => if bad (whirField c.val 0) then 1 else 0) ≤
      2^hi * (B * (2^400 / quinticGoldilocksCard + 1)) := by
  let pool := (List.range (2^400)).map decodeQuintic400
  let S := dedupEq (pool.filter bad)
  have hcard := hc S (dedupEq_nodup _) (fun t ht => (List.mem_filter.mp ((mem_dedupEq _ _).mp ht)).2)
  apply Nat.le_trans (qsum_le_qsum (g := fun c => if S.any (fun z => decide (whirField c.val 0 = z)) then 1 else 0) ?_)
  · exact Nat.le_trans (whirField_fold_bad_seeds hi S) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcard))
  · intro c
    cases h : bad (whirField c.val 0) with
    | false => exact Nat.zero_le _
    | true =>
      have hp : whirField c.val 0 ∈ pool := List.mem_map.mpr
        ⟨c.val % 2^400, List.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos _)), by simp [whirField]⟩
      have hm : whirField c.val 0 ∈ S := (mem_dedupEq _ _).mpr (List.mem_filter.mpr ⟨hp, h⟩)
      have ha : S.any (fun z => decide (whirField c.val 0 = z)) = true :=
        List.any_eq_true.mpr ⟨_, hm, by simp⟩
      rw [ha]; decide

/-- Exact independence of the 32-bit position slices from the low 2000 field bits.
    A fixed set of B positions in a two-adic domain is hit on every draw with
    probability at most (B/2^s)^t. -/
theorem whirPosition_all_good_seeds (s t B : Nat) (hs : s ≤ 32) (good : Nat → Bool)
    (hg : qsum (2^s) (fun i => if good i.val then 1 else 0) ≤ B) :
    qsum ((2^32)^t * 2^2000) (fun c => if (List.range t).all (fun j =>
      good (whirPosition c.val j (2^s))) then 1 else 0) ≤
      (2^(32-s)*B)^t * 2^2000 := by
  let f := fun u => if (List.range t).all (fun j => good (((u / (2^32)^j) % 2^32) % 2^s))
    then 1 else 0
  have hp (c j : Nat) : whirPosition c j (2^s) =
      (((c / 2^2000 / (2^32)^j) % 2^32) % 2^s) := by
    rw [whirPosition, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_mul, Nat.pow_add]
  have h1 := qsum_mul_div_mod_eq ((2^32)^t) (2^2000) (Nat.two_pow_pos _) (fun hi _ => f hi)
  change qsum _ _ ≤ _
  simp only [hp]
  change qsum _ (fun c => f (c.val / 2^2000)) ≤ _
  rw [h1]
  simp only [qsum_const, Nat.mul_comm (2^2000), qsum_mul_right]
  apply Nat.mul_le_mul_right
  apply qsum_good_digits_le (2^32) t _ (Nat.two_pow_pos _) (fun i => good (i % 2^s))
  rw [qsum_mul_mod_eq (show 2^32 = 2^(32-s)*2^s by rw [← Nat.pow_add]; congr 1; omega)
    (Nat.two_pow_pos _) _ (fun i => if good i then 1 else 0) (fun _ => rfl)]
  exact Nat.mul_le_mul_left _ hg

/-- Position in a high-bit query word after removing the independent low 2000 bits. -/
def shiftPos (s word j : Nat) : Nat := ((word / (2^32)^j) % 2^32) % 2^s

theorem whirPosition_high (s c j : Nat) : whirPosition c j (2^s) = shiftPos s (c / 2^2000) j := by
  rw [whirPosition, shiftPos, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_mul, Nat.pow_add]

private theorem whirField_low (c : Nat) : whirField c 0 = whirField (c % 2^2000) 0 := by
  unfold whirField
  simp only [Nat.zero_mod, Nat.mul_zero, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (show 2^400 ∣ 2^2000 by exact Nat.pow_dvd_pow 2 (by decide))]

/-- Combine the independent positional miss event and the field root count.
    The root polynomial may depend on the entire sampled query vector. -/
theorem shift_field_mass (s t B R : Nat) (hs : s ≤ 32) (good : Nat → Bool)
    (hg : qsum (2^s) (fun j => if good j.val then 1 else 0) ≤ B)
    (live : Nat → K → Bool)
    (roots : ∀ u, (List.range t).all (fun j => good (shiftPos s u j)) = false →
      ∀ S : List K, S.Nodup → (∀ z ∈ S, live u z = true) → S.length ≤ R) :
    qsum ((2^32)^t * 2^2000) (fun c => if live (c.val / 2^2000) (whirField c.val 0) then 1 else 0) ≤
      (2^(32-s)*B)^t * 2^2000 + (2^32)^t * (2^1600 * (R * (2^400/quinticGoldilocksCard+1))) := by
  let allG := fun u => (List.range t).all fun j => good (shiftPos s u j)
  let rate := 2^1600 * (R * (2^400/quinticGoldilocksCard+1))
  let score := fun u (z : K) => if live u z then 1 else 0
  have split (f : Nat → Nat → Nat) := qsum_mul_div_mod_eq ((2^32)^t) (2^2000) (Nat.two_pow_pos _) f
  have pcount := whirPosition_all_good_seeds s t B hs good hg
  simp only [whirPosition_high] at pcount
  change qsum _ (fun c => if allG (c.val / 2^2000) then 1 else 0) ≤ _ at pcount
  rw [split (fun u _ => if allG u then 1 else 0)] at pcount
  simp only [qsum_const] at pcount
  change qsum _ (fun c => score (c.val / 2^2000) (whirField c.val 0)) ≤ _
  rw [qsum_congr (fun c => congrArg (score (c.val / 2^2000)) (whirField_low c.val)),
    split (fun u v => score u (whirField v 0))]
  have row (u : Fin ((2^32)^t)) : qsum (2^2000) (fun v => score u.val (whirField v.val 0)) ≤
      2^2000 * (if allG u.val then 1 else 0) + rate := by
    cases h : allG u.val with
    | false =>
      change _ ≤ 0 + rate
      rw [Nat.zero_add]
      exact whirField_predicate_mass 1600 R (live u.val) (roots u.val h)
    | true =>
      have oneBound := qsum_le_qsum (g := fun _ : Fin (2^2000) => 1) (fun v =>
        show score u.val (whirField v.val 0) ≤ 1 by dsimp only [score]; split <;> decide)
      rw [qsum_const] at oneBound
      exact Nat.le_trans oneBound (Nat.le_add_right _ _)
  have h := qsum_le_qsum row
  rw [qsum_add, qsum_const] at h
  exact Nat.le_trans h (Nat.add_le_add_right pcount _)

/-! ## WHIR domains and sumcheck kernels -/

def domainLog (stages : List WhirStage) (i : Nat) : Nat :=
  match stages[i]? with
  | some st => st.logDomain + st.foldK
  | none => (stages.getLast?).elim 0 WhirStage.logDomain

/-- A kernel term (w,z) acts on P by w·P(z). For P=E(X²)+X·O(X²)
    the sumcheck polynomial is w·((1-z)+t·(2z-1))·(E(z²)+t·O(z²)).
    Its evaluations at zero and one sum to w·P(z). -/
def foldKernelTerm (α : K) (term : K × K) : K × K :=
  let (w, z) := term
  (w *ᵍ ((one -ᵍ z) +ᵍ α *ᵍ ((z +ᵍ z) -ᵍ one)), z *ᵍ z)

theorem foldKernelTerm_endpoints (w z e o : K) :
    (foldKernelTerm zero (w,z)).1 *ᵍ e +ᵍ
    (foldKernelTerm one (w,z)).1 *ᵍ (e +ᵍ o) = w *ᵍ (e +ᵍ z *ᵍ o) := by
  dsimp only [foldKernelTerm]
  constructive_ring

def kernelValue (P : List K) : List (K × K) → K
  | [] => zero
  | (w,z) :: ts => w *ᵍ RoundPoly.evalCoeffs P z +ᵍ kernelValue P ts

theorem kernelValue_foldl (P : List K) (terms : List (K × K)) (a : K) :
    terms.foldl (fun s t => s +ᵍ t.1 *ᵍ RoundPoly.evalCoeffs P t.2) a = a +ᵍ kernelValue P terms := by
  induction terms generalizing a with
  | nil => simp only [List.foldl_nil, kernelValue, LawfulCommRing.add_zero]
  | cons t ts ih => rcases t with ⟨w,z⟩; rw [List.foldl_cons, ih, kernelValue]; constructive_ring

/-- The residual claim is quadratic in the challenge for every finite kernel.
    Its endpoint sum is the original kernel claim. -/
theorem kernel_fold_quadratic (P : List K) (terms : List (K × K)) :
    ∃ a b c : K, (∀ t, kernelValue (foldPolyCoeffs t P) (terms.map (foldKernelTerm t)) =
      a +ᵍ t *ᵍ (b +ᵍ t *ᵍ c)) ∧
      a +ᵍ (a +ᵍ (b +ᵍ c)) = kernelValue P terms := by
  induction terms with
  | nil =>
    refine ⟨zero,zero,zero,?_,?_⟩ <;> simp only [List.map_nil, kernelValue] <;> intros <;> constructive_ring
  | cons term rest ih =>
    rcases term with ⟨w,z⟩
    obtain ⟨a,b,c,ht,hs⟩ := ih
    obtain ⟨e,o,hp,_,hf⟩ := eval_split z P
    let u := one -ᵍ z
    let v := (z +ᵍ z) -ᵍ one
    refine ⟨a +ᵍ w *ᵍ u *ᵍ e, b +ᵍ w *ᵍ (v *ᵍ e +ᵍ u *ᵍ o), c +ᵍ w *ᵍ v *ᵍ o, ?_, ?_⟩
    · intro t
      simp only [List.map_cons, foldKernelTerm, kernelValue, hf, ht]
      dsimp only [u,v]; constructive_ring
    · rw [kernelValue, hp, ← hs]
      dsimp only [u,v]; constructive_ring

/-- A degree-two message with the wrong endpoint sum agrees with the honest
    residual claim on at most two distinct field challenges. -/
theorem kernel_wrong_claim_challenges (P msg : List K) (terms : List (K × K)) (S : List K)
    (hs : S.Nodup) (hlen : msg.length ≤ 3)
    (hwrong : RoundPoly.evalCoeffs msg zero +ᵍ RoundPoly.evalCoeffs msg one ≠ kernelValue P terms)
    (hhit : ∀ t ∈ S, RoundPoly.evalCoeffs msg t =
      kernelValue (foldPolyCoeffs t P) (terms.map (foldKernelTerm t))) : S.length ≤ 2 := by
  apply Nat.le_of_not_gt
  intro h
  obtain ⟨a,b,c,ht,hsum⟩ := kernel_fold_quadratic P terms
  have ev (t : K) : RoundPoly.evalCoeffs [a,b,c] t = a +ᵍ t *ᵍ (b +ᵍ t *ᵍ c) := by
    simp only [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil]; constructive_ring
  have he := trimPoly_eq_of_agree_on_nodup (d := 2) (P := msg) (Q := [a,b,c])
    hlen (by exact Nat.le_refl 3) hs h (fun t hm => by rw [hhit t hm, ht, ev])
  have eq (t : K) : RoundPoly.evalCoeffs msg t = RoundPoly.evalCoeffs [a,b,c] t := by
    rw [← evalCoeffs_trimPoly t msg, he, evalCoeffs_trimPoly]
  apply hwrong
  rw [eq zero, eq one, ev, ev, ← hsum]; constructive_ring

private def weightedFrom (γ : K) : K → List K → List (K × K)
  | _, [] => []
  | w, z :: zs => (w,z) :: weightedFrom γ (w *ᵍ γ) zs

def weightedPoints (γ : K) (points : List K) : List (K × K) :=
  if γ = zero then [] else weightedFrom γ γ points

private theorem kernelValue_append (P : List K) (a b : List (K × K)) :
    kernelValue P (a ++ b) = kernelValue P a +ᵍ kernelValue P b := by
  induction a with
  | nil => rw [List.nil_append, kernelValue, LawfulCommRing.zero_add]
  | cons t ts ih =>
    rcases t with ⟨w,z⟩; rw [List.cons_append, kernelValue, kernelValue, ih]; constructive_ring

private theorem kernelValue_weighted (P : List K) (γ w : K) (pts : List K) :
    kernelValue P (weightedFrom γ w pts) = w *ᵍ RoundPoly.evalCoeffs (pts.map (RoundPoly.evalCoeffs P)) γ := by
  induction pts generalizing w with
  | nil => rw [weightedFrom, kernelValue, List.map_nil, RoundPoly.evalCoeffs_nil, LawfulCommRing.mul_zero]
  | cons z zs ih => rw [weightedFrom, kernelValue, ih, List.map_cons, RoundPoly.evalCoeffs_cons]; constructive_ring

/-- The actual shift/OOD combiner and terminal kernel evaluate the same polynomial
    in the answer-round challenge on honest readings. -/
theorem kernelValue_batch (P : List K) (γ : K) (pts : List K) (terms : List (K × K)) :
    kernelValue P (terms ++ weightedPoints γ pts) =
      combineClaim (kernelValue P terms) γ (pts.map (RoundPoly.evalCoeffs P)) := by
  rw [kernelValue_append, combineClaim_eq_eval, RoundPoly.evalCoeffs_cons, weightedPoints]
  split
  · rename_i h; rw [h, kernelValue, LawfulCommRing.zero_mul]
  · rw [kernelValue_weighted]

/-- Fix the OOD points and query positions before testing the independent combiner.
    If any coefficient of the claimed readings differs, at most their length many
    distinct γ values can repair the combined claim. -/
theorem batch_wrong_claim_challenges (P : List K) (terms : List (K × K)) (pts vals : List K) (cl : K)
    (hLen : vals.length = pts.length)
    (hDiff : trimPoly (cl :: vals) ≠ trimPoly (kernelValue P terms :: pts.map (RoundPoly.evalCoeffs P)))
    (S : List K) (hs : S.Nodup) (hhit : ∀ γ ∈ S,
      combineClaim cl γ vals = kernelValue P (terms ++ weightedPoints γ pts)) :
    S.length ≤ pts.length := by
  apply Nat.le_of_not_gt
  intro h
  apply hDiff
  apply trimPoly_eq_of_agree_on_nodup (d := pts.length) (U := S)
    (by simp only [List.length_cons, hLen]; exact Nat.le_refl _)
    (by simp only [List.length_cons, List.length_map]; exact Nat.le_refl _) hs h
  intro γ hm
  rw [← combineClaim_eq_eval, ← combineClaim_eq_eval, hhit γ hm, kernelValue_batch]

private theorem eq_of_length_trim {P Q : List K} (hlen : P.length = Q.length)
    (he : trimPoly P = trimPoly Q) : P = Q := by
  apply List.ext_getElem hlen
  intro i hp hq
  have h := (trimPoly_eq_iff_coeffAt P Q).mp he i
  simpa only [coeffAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp,
    List.getElem?_eq_getElem hq, Option.getD_some] using h

def shiftPositions (s t u : Nat) := (List.range t).map (shiftPos s u)

def shiftBatchLive (s t u : Nat) (P : List K) (terms : List (K × K)) (cl : K)
    (zs ys : List K) (prev : Nat → K) (γ : K) : Bool :=
  let qs := shiftPositions s t u
  decide (combineClaim cl γ (ys ++ qs.map prev) =
    kernelValue P (terms ++ weightedPoints γ (zs ++ qs.map (cosetPoint s))))

/-- Conditional shift probability for one candidate fixed by the commit round.
    Failed positional checks can only be repaired at roots of the independent
    response combiner polynomial. The earlier OOD answer was fixed before both. -/
theorem shiftBatchLive_mass (s t B : Nat) (hs : s ≤ 32) (P : List K) (terms : List (K × K))
    (cl : K) (zs ys : List K) (prev : Nat → K) (hlen : ys.length = zs.length)
    (hg : qsum (2^s) (fun i => if cl = kernelValue P terms ∧
      prev i.val = RoundPoly.evalCoeffs P (cosetPoint s i.val) then 1 else 0) ≤ B) :
    qsum ((2^32)^t * 2^2000) (fun c => if shiftBatchLive s t (c.val / 2^2000) P terms cl zs ys prev
      (whirField c.val 0) then 1 else 0) ≤
      (2^(32-s)*B)^t * 2^2000 +
      (2^32)^t * (2^1600 * ((zs.length+t) * (2^400/quinticGoldilocksCard+1))) := by
  let good := fun i => decide (cl = kernelValue P terms ∧ prev i = RoundPoly.evalCoeffs P (cosetPoint s i))
  apply shift_field_mass s t B (zs.length+t) hs good (by simpa only [good, decide_eq_true_eq] using hg)
    (fun u γ => shiftBatchLive s t u P terms cl zs ys prev γ)
  intro u hb S hn hh
  let qs := shiftPositions s t u
  let pts := zs ++ qs.map (cosetPoint s)
  let vals := ys ++ qs.map prev
  have hsz : pts.length = zs.length+t := by simp [pts, qs, shiftPositions]
  rw [← hsz]
  apply batch_wrong_claim_challenges P terms pts vals cl (by simp [pts, vals, hlen])
  · intro he
    have eq := eq_of_length_trim (P := cl::vals) (Q := kernelValue P terms::pts.map (RoundPoly.evalCoeffs P))
      (by simp [pts, vals, hlen]) he
    have e := List.cons.inj eq
    have tail := congrArg (List.drop zs.length) e.2
    have et : qs.map prev = qs.map (fun j => RoundPoly.evalCoeffs P (cosetPoint s j)) := by
      simpa [pts, vals, List.map_append, ← hlen, Function.comp_def] using tail
    have ha : (List.range t).all (fun j => good (shiftPos s u j)) = true := by
      apply List.all_eq_true.mpr
      intro j hj
      exact decide_eq_true ⟨e.1, List.map_inj_left.mp et _ (List.mem_map.mpr ⟨j,hj,rfl⟩)⟩
    rw [hb] at ha; contradiction
  · exact hn
  · exact fun γ hm => of_decide_eq_true (hh γ hm)

/-- Transport all outstanding evaluations through the fold challenges and add
    the OOD and shift claims in exactly the order consumed by combineClaim. -/
private def terminalKernel : List WhirStage → List (StageView K) → List (K × K) → K
  | st :: rest, v :: vs, terms =>
    let folded := v.folds.foldl (fun ts r => ts.map (foldKernelTerm (whirField r.2 0))) terms
    if rest.isEmpty then
      folded.foldl (fun acc t => acc +ᵍ t.1 *ᵍ RoundPoly.evalCoeffs v.commit.1.poly t.2) zero
    else
      let ood := (List.range st.oodCount).map (whirField v.commit.2)
      let shifts := (List.range st.queryCount).map fun j =>
        cosetPoint st.logDomain (whirPosition v.answer.2 j st.domainSize)
      terminalKernel rest vs (folded ++ weightedPoints (whirField v.answer.2 st.queryCount) (ood ++ shifts))
  | _, _, _ => zero

def quinticEnv (stages : List WhirStage) (d : Nat) : WhirEnv K where
  chalField := whirField
  chalPos := whirPosition
  domPt := fun i => cosetPoint (domainLog stages i)
  fold2 := quinticWhirFold2
  fiberPoint := some fiberPoint
  initClaim := fun p => RoundPoly.evalCoeffs p one
  finalClaim := fun p _ => RoundPoly.evalCoeffs p one
  finalClaimViews := some (fun vs _ => terminalKernel stages vs [(one, one)])
  finalDeg := d

def packedQuinticWhirEnv (logCells : Nat) : WhirEnv K :=
  let stages := (packedProdSched logCells).stages
  quinticEnv stages (2 ^ (logCells - (stages.map WhirStage.foldK).sum) + 1)

/-- Every supported packed schedule fits the decoded field and position slices
    and the two-adic domain, with a nonempty fold block at each stage. -/
theorem packedQuinticWhir_geometry (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) :
    let ss := (packedProdSched n).stages
    3 ≤ ss.length ∧ ss.length ≤ 4 ∧ ss.all (fun st =>
      decide (0 < st.foldK ∧ st.logDomain + st.foldK ≤ 32 ∧ 0 < st.queryCount ∧
        st.queryCount ≤ 267 ∧ 0 < st.oodCount ∧ st.oodCount ≤ 5)) = true := by
  have h : n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨
    n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst n <;> decide +kernel

/-- For every stage of all thirteen packed schedules, count the position words
    that hit a chosen set on every query. The low five field slices are free. -/
theorem packedStage_query_hit_bound (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : WhirStage) (mem : st ∈ (packedProdSched n).stages) (B : Nat) (good : Nat → Bool)
    (bound : qsum (2^st.logDomain) (fun i => if good i.val then 1 else 0) ≤ B) :
    qsum ((2^32)^st.queryCount * 2^2000) (fun c => if (List.range st.queryCount).all
        (fun j => good ((packedQuinticWhirEnv n).chalPos c.val j (2^st.logDomain)))
      then 1 else 0) ≤ (2^(32-st.logDomain)*B)^st.queryCount * 2^2000 := by
  have geom := of_decide_eq_true (List.all_eq_true.mp (packedQuinticWhir_geometry n lo hi).2.2 st mem)
  exact whirPosition_all_good_seeds _ _ B (by omega) good bound

/-- Width of five field draws and the maximum number of 32-bit position draws. -/
@[expose] def packedChallengeBits : Nat := 2000 + 32 * 267

private theorem position_digit_mod (c a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    c % (a*b) / a = c / a % b := by
  have hr := Nat.mod_lt c (Nat.mul_pos ha hb)
  have hd := Nat.div_add_mod (c % (a*b)) a
  have lt : c % (a*b) / a < b := by
    by_cases h : b ≤ c % (a*b) / a
    · have hm := Nat.mul_le_mul_left a h
      omega
    · omega
  conv => rhs; rw [← Nat.mod_add_div c (a*b)]
  rw [Nat.mul_assoc, Nat.add_mul_div_left _ _ ha, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lt]

/-- Count the full-width challenge words whose sampled positions all hit the
    chosen set. Unused high bits contribute the same multiplicity to each event. -/
theorem packedStage_full_width_query_bound (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : WhirStage) (mem : st ∈ (packedProdSched n).stages) (B : Nat) (good : Nat → Bool)
    (bound : qsum (2^st.logDomain) (fun i => if good i.val then 1 else 0) ≤ B) :
    qsum (2^packedChallengeBits) (fun c => if (List.range st.queryCount).all
        (fun j => good ((packedQuinticWhirEnv n).chalPos c.val j (2^st.logDomain)))
      then 1 else 0) ≤
      2^(32*(267-st.queryCount)) * ((2^(32-st.logDomain)*B)^st.queryCount * 2^2000) := by
  let t := st.queryCount
  let used := 2000 + 32*t
  have geom := of_decide_eq_true (List.all_eq_true.mp (packedQuinticWhir_geometry n lo hi).2.2 st mem)
  have room : t ≤ 267 := geom.2.2.2.1
  have width : 2^packedChallengeBits = 2^(32*(267-t)) * 2^used := by
    rw [← Nat.pow_add]; congr 1; dsimp [packedChallengeBits, used]; omega
  have trunc (c j : Nat) (hj : j < t) :
      whirPosition (c % 2^used) j (2^st.logDomain) = whirPosition c j (2^st.logDomain) := by
    let start := 2000 + 32*j
    have split : 2^used = 2^start * 2^(used-start) := by
      rw [← Nat.pow_add]; congr 1; dsimp [used,start]; omega
    simp only [whirPosition, Nat.shiftRight_eq_div_pow]
    change (c % 2^used / 2^start % 2^32) % _ = (c / 2^start % 2^32) % _
    rw [split, position_digit_mod _ _ _ (Nat.two_pow_pos _) (Nat.two_pow_pos _),
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show 32 ≤ used-start by dsimp [used,start]; omega))]
  let hit := fun c => if (List.range t).all (fun j => good (whirPosition c j (2^st.logDomain))) then 1 else 0
  have same (c : Nat) : hit c = hit (c % 2^used) := by
    have eq : (List.range t).all (fun j => good (whirPosition (c % 2^used) j (2^st.logDomain))) =
        (List.range t).all (fun j => good (whirPosition c j (2^st.logDomain))) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro h j hj <;> specialize h j hj <;>
        simpa only [trunc c j (List.mem_range.mp hj)] using h
    simp only [hit, eq]
  change qsum _ (fun c => hit c.val) ≤ _
  rw [qsum_mul_mod_eq width (Nat.two_pow_pos _) _ hit (fun c => same c.val)]
  apply Nat.mul_le_mul_left
  have core := packedStage_query_hit_bound n lo hi st mem B good bound
  have words : 2^used = (2^32)^t * 2^2000 := by rw [← Nat.pow_mul, ← Nat.pow_add]; congr 1; dsimp [used]; omega
  rw [words]
  exact core

#verify_constructive packedStage_query_hit_bound packedStage_full_width_query_bound

/-- Degree bounds, agreement thresholds and query counts for the 256-point schedule. -/
@[expose] def zkHemV2MultiStageSched : WhirVerifierSchedule :=
  ⟨8, quinticGoldilocksCard, quinticGoldilocksCard_pos,
    [⟨1, 7, 4, 1, 640, 8, 88, 1, 4, 8, 2, 256⟩,
     ⟨1, 6, 4, 1, 640, 4, 44, 1, 4, 8, 2, 256⟩,
     ⟨1, 5, 4, 1, 640, 2, 22, 1, 4, 8, 2, 256⟩]⟩

def zkHemV2MultiStageEnv : WhirEnv K := quinticEnv zkHemV2MultiStageSched.stages 1

theorem zkHemV2MultiStage_geometry :
    zkHemV2MultiStageSched.numRounds = 9 ∧ zkHemV2MultiStageSched.johnsonOk = true ∧
    ([0,1,2,3].map (domainLog zkHemV2MultiStageSched.stages)) = [8,7,6,5] := by
  decide +kernel

theorem zkHemV2MultiStage_tree_qrom_lt_128_at_2pow64 (prof : WhirCommitmentProfile)
    {d Q : Nat} (hd : d ≤ 16) (hQ : Q ≤ 2 ^ 64) :
    RatBound.lt
      (RatBound.add (RatBound.scale (2 ^ (d + 1) - 1) (scheduleQromError zkHemV2MultiStageSched Q))
        (merkleProfileQromBound prof Q)) (RatBound.invPow2 128) := by
  have hn : 2 ^ (d + 1) - 1 ≤ 131071 := by
    have : 2 ^ (d + 1) ≤ 2 ^ 17 := Nat.pow_le_pow_right (by decide) (show d + 1 ≤ 17 by omega)
    omega
  have hm := scheduleQromError_mono zkHemV2MultiStageSched hQ
  have scale : RatBound.le
      (RatBound.scale (2 ^ (d + 1) - 1) (scheduleQromError zkHemV2MultiStageSched Q))
      (RatBound.scale 131071 (scheduleQromError zkHemV2MultiStageSched (2 ^ 64))) := by
    unfold RatBound.le at hm ⊢
    dsimp only [RatBound.scale]
    simp only [Nat.mul_assoc]
    exact Nat.mul_le_mul hn hm
  apply ratBound_lt_of_le_of_lt_packed (RatBound.add_le_add scale
    (RatBound.le_trans (merkleProfileQromBound_mono prof hQ) (merkleProfileQromBound_le_400 prof _)))
  rw [scheduleQromError_eq, WhirVerifierSchedule.roundBounds_eq]
  simp only [zkHemV2MultiStageSched, stagesRoundBounds_cons, stagesRoundBounds_nil,
    WhirStage.roundBounds_eq, WhirStage.foldBound_eq, WhirStage.oodBound_eq, WhirStage.shiftBound_eq,
    binom2_eq]
  decide +kernel

/-! ## Exceptional fold challenges and table agreement -/

/-- Specialize the three-response estimate to actual quintic antipodal openings. -/
theorem quinticFold_exceptional_challenges (D S : List K) (k A : Nat)
    (root pos negVal : K → K) (Q : K → List K) (hd : D.Nodup) (hs : S.Nodup)
    (hk : 0 < k) (hTriple : 2 * D.length + k ≤ 3 * A)
    (hQ : ∀ t ∈ S, (Q t).length ≤ k ∧ A ≤ (D.filter (fun z => decide
      (RoundPoly.evalCoeffs (Q t) z = quinticWhirFold2 (root z) t (pos z) (negVal z)))).length)
    (hfar : ∀ E O : List K, E.length ≤ k → O.length ≤ k →
      (D.filter (fun z => decide
        (RoundPoly.evalCoeffs E z = (pos z +ᵍ negVal z) *ᵍ LawfulField.inv (one +ᵍ one) ∧
         RoundPoly.evalCoeffs O z = (pos z -ᵍ negVal z) *ᵍ LawfulField.inv ((one +ᵍ one) *ᵍ root z)))).length < A) :
    S.length ≤ max 1 D.length := by
  apply binaryFold_exceptional_challenges D S k A _ _ Q hd hs hk hTriple _ hfar
  intro t ht
  refine ⟨(hQ t ht).1, ?_⟩
  change A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs (Q t) z =
    (pos z +ᵍ negVal z) *ᵍ LawfulField.inv (one +ᵍ one) +ᵍ
    t *ᵍ ((pos z -ᵍ negVal z) *ᵍ LawfulField.inv ((one +ᵍ one) *ᵍ root z))))).length
  simpa only [quinticWhirFold2, LawfulCommRing.mul_assoc] using (hQ t ht).2

/-- Degree-<k candidates of the actual folded word at a given field challenge. -/
def foldCandidates (D : List K) (k A : Nat) (root pos negVal : K → K) (t : K) :
    List (GsUniPoly K) :=
  gsDecodeList (k-1) A D (fun z => quinticWhirFold2 (root z) t (pos z) (negVal z))

private theorem kernelValue_congr {P Q : List K} (h : ∀ z, RoundPoly.evalCoeffs P z = RoundPoly.evalCoeffs Q z)
    (terms : List (K × K)) : kernelValue P terms = kernelValue Q terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih => rcases t with ⟨w,z⟩; simp only [kernelValue, h, ih]

/-- If a scalar polynomial agrees on A antipodal pairs, every close folded
    candidate has its evaluation everywhere inside the unique decoding radius. -/
theorem close_candidate_fold_eq (D : List K) (k A : Nat) (root pos negVal : K → K)
    (hd : D.Nodup) (hk : 0 < k) (hA : k ≤ A) (hOverlap : D.length+k ≤ 2*A)
    (hx : ∀ z ∈ D, root z ≠ zero ∧ root z *ᵍ root z = z)
    (P : List K) (hP : P.length ≤ 2*k)
    (hClose : A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs P (root z) = pos z ∧
      RoundPoly.evalCoeffs P (neg (root z)) = negVal z))).length)
    (α : K) (Q : GsUniPoly K) (hm : Q ∈ foldCandidates D k A root pos negVal α) :
    ∀ z, RoundPoly.evalCoeffs Q.coeffs z = RoundPoly.evalCoeffs (foldPolyCoeffs α P) z := by
  let g := fun z => decide (RoundPoly.evalCoeffs P (root z) = pos z ∧
      RoundPoly.evalCoeffs P (neg (root z)) = negVal z)
  let f := fun z => decide (RoundPoly.evalCoeffs Q.coeffs z = quinticWhirFold2 (root z) α (pos z) (negVal z))
  have spec := (mem_gsDecodeList_iff _ hd (d := k-1) (A := A) (by omega) Q).mp hm
  have hq : A ≤ (D.filter f).length := spec.2
  change A ≤ (D.filter g).length at hClose
  have lower := filter_overlap_len g f D
  have he := trimPoly_eq_of_agree_on_nodup (d := k-1) (P := Q.coeffs) (Q := foldPolyCoeffs α P)
    spec.1 (by rw [foldPolyCoeffs_length]; omega)
    (U := D.filter (fun z => g z && f z)) (List.Pairwise.filter _ hd) (by omega) (fun z hz => by
      obtain ⟨hdz, hgf⟩ := List.mem_filter.mp hz
      obtain ⟨hg,hf⟩ := Bool.and_eq_true_iff.mp hgf
      obtain ⟨hp,hn⟩ := of_decide_eq_true hg
      obtain ⟨hne,hs⟩ := hx z hdz
      rw [of_decide_eq_true hf, ← hp, ← hn, quinticWhirFold2_evalCoeffs _ _ _ hne, hs])
  intro z
  rw [← evalCoeffs_trimPoly z Q.coeffs, he, evalCoeffs_trimPoly]

/-- The other fold-round case: a jointly close input polynomial with the wrong
    claim can produce an agreeing residual witness at only two distinct challenges. -/
theorem close_fold_wrong_claim (D : List K) (k A : Nat) (root pos negVal : K → K)
    (hd : D.Nodup) (hk : 0 < k) (hA : k ≤ A) (hOverlap : D.length+k ≤ 2*A)
    (hx : ∀ z ∈ D, root z ≠ zero ∧ root z *ᵍ root z = z)
    (P : List K) (hP : P.length ≤ 2*k)
    (hClose : A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs P (root z) = pos z ∧
      RoundPoly.evalCoeffs P (neg (root z)) = negVal z))).length)
    (terms : List (K × K)) (msg S : List K) (hs : S.Nodup) (hlen : msg.length ≤ 3)
    (hwrong : RoundPoly.evalCoeffs msg zero +ᵍ RoundPoly.evalCoeffs msg one ≠ kernelValue P terms)
    (hhit : ∀ t ∈ S, ∃ Q ∈ foldCandidates D k A root pos negVal t, RoundPoly.evalCoeffs msg t =
      kernelValue Q.coeffs (terms.map (foldKernelTerm t))) : S.length ≤ 2 := by
  apply kernel_wrong_claim_challenges P msg terms S hs hlen hwrong
  intro t ht
  obtain ⟨Q, hm, hq⟩ := hhit t ht
  exact hq.trans (kernelValue_congr (close_candidate_fold_eq D k A root pos negVal hd hk hA hOverlap hx P hP hClose t Q hm) _)

/-- Count every seed with a close folded polynomial. The constructive RS decoder
    supplies the witnesses used by the three-response bound. -/
theorem foldRound_exception_mass (hi : Nat) (D : List K) (k A : Nat)
    (root pos negVal : K → K) (hd : D.Nodup) (hk : 0 < k) (hA : k ≤ A)
    (hTriple : 2 * D.length + k ≤ 3 * A)
    (hfar : ∀ E O : List K, E.length ≤ k → O.length ≤ k →
      (D.filter (fun z => decide
        (RoundPoly.evalCoeffs E z = (pos z +ᵍ negVal z) *ᵍ LawfulField.inv (one +ᵍ one) ∧
         RoundPoly.evalCoeffs O z = (pos z -ᵍ negVal z) *ᵍ LawfulField.inv ((one +ᵍ one) *ᵍ root z)))).length < A) :
    qsum (2^(hi+400)) (fun c => if (foldCandidates D k A root pos negVal (whirField c.val 0)).isEmpty
      then 0 else 1) ≤ 2^hi * (max 1 D.length * (2^400 / quinticGoldilocksCard + 1)) := by
  let C := foldCandidates D k A root pos negVal
  let pool := (List.range (2^400)).map decodeQuintic400
  let S := dedupEq (pool.filter fun t => !(C t).isEmpty)
  let Q := fun t => (C t).head?.elim [] (fun p => p.coeffs)
  have hk' : k-1+1 = k := by omega
  have hcard := quinticFold_exceptional_challenges D S k A root pos negVal Q hd
    (dedupEq_nodup _) hk hTriple (by
      intro t ht
      have hn := (List.mem_filter.mp ((mem_dedupEq _ _).mp ht)).2
      cases hc : C t with
      | nil => simp [hc] at hn
      | cons p ps =>
        have hm : p ∈ C t := hc ▸ List.mem_cons_self
        have spec := (mem_gsDecodeList_iff _ hd (d := k-1) (A := A) (by omega) p).mp hm
        simpa only [Q, hc, List.head?_cons, Option.elim_some, hk'] using spec) hfar
  apply Nat.le_trans (qsum_le_qsum (g := fun c => if S.any (fun z => decide (whirField c.val 0 = z)) then 1 else 0) ?_)
  · exact Nat.le_trans (whirField_fold_bad_seeds hi S)
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcard))
  · intro c
    change (if (C (whirField c.val 0)).isEmpty then 0 else 1) ≤ _
    cases hc : (C (whirField c.val 0)).isEmpty with
    | true => exact Nat.zero_le _
    | false =>
      have hp : whirField c.val 0 ∈ pool := by
        apply List.mem_map.mpr
        exact ⟨c.val % 2^400, List.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos _)),
          by simp [whirField]⟩
      have hm : whirField c.val 0 ∈ S := (mem_dedupEq _ _).mpr (List.mem_filter.mpr ⟨hp, by simp [hc]⟩)
      have ha : S.any (fun z => decide (whirField c.val 0 = z)) = true :=
        List.any_eq_true.mpr ⟨_, hm, by simp⟩
      rw [ha]; decide

/-- Interleaving close even and odd evaluations recovers both original scalar readings. -/
theorem interleave_recovers_pair (E O : List K) (x a b : K) (hx : x ≠ zero)
    (he : RoundPoly.evalCoeffs E (x *ᵍ x) = (a +ᵍ b) *ᵍ LawfulField.inv (one +ᵍ one))
    (ho : RoundPoly.evalCoeffs O (x *ᵍ x) = (a -ᵍ b) *ᵍ LawfulField.inv ((one +ᵍ one) *ᵍ x)) :
    RoundPoly.evalCoeffs (interleavePoly E O) x = a ∧
      RoundPoly.evalCoeffs (interleavePoly E O) (neg x) = b := by
  let two : K := one +ᵍ one
  have hn : two ≠ zero := by decide +kernel
  have hi := LawfulField.mul_inv_cancel hn
  have hix := LawfulField.mul_inv_cancel (mul_nonzero hn hx)
  have inv : x *ᵍ LawfulField.inv (two *ᵍ x) = LawfulField.inv two := by
    calc
      _ = (two *ᵍ LawfulField.inv two) *ᵍ (x *ᵍ LawfulField.inv (two *ᵍ x)) := by rw [hi, LawfulCommRing.one_mul]
      _ = ((two *ᵍ x) *ᵍ LawfulField.inv (two *ᵍ x)) *ᵍ LawfulField.inv two := by constructive_ring
      _ = _ := by rw [hix, LawfulCommRing.one_mul]
  have odd : x *ᵍ RoundPoly.evalCoeffs O (x *ᵍ x) = (a -ᵍ b) *ᵍ LawfulField.inv two := by
    rw [ho, ← inv]; dsimp only [two]; constructive_ring
  have sq : neg x *ᵍ neg x = x *ᵍ x := by constructive_ring
  rw [evalCoeffs_interleavePoly, evalCoeffs_interleavePoly, sq, he]
  constructor
  · rw [odd]
    calc
      _ = a *ᵍ (two *ᵍ LawfulField.inv two) := by dsimp only [two]; constructive_ring
      _ = _ := by rw [hi, LawfulCommRing.mul_one]
  · calc
      _ = RoundPoly.evalCoeffs E (x *ᵍ x) -ᵍ x *ᵍ RoundPoly.evalCoeffs O (x *ᵍ x) := by rw [he]; constructive_ring
      _ = b *ᵍ (two *ᵍ LawfulField.inv two) := by rw [he, odd]; dsimp only [two]; constructive_ring
      _ = _ := by rw [hi, LawfulCommRing.mul_one]

/-- Fold-round seed mass when every degree-<2k polynomial misses the required
    number of antipodal pairs of the original word. -/
theorem antipodal_foldRound_mass (hi : Nat) (D : List K) (k A : Nat)
    (root pos negVal : K → K) (hd : D.Nodup) (hk : 0 < k) (hA : k ≤ A)
    (hTriple : 2 * D.length + k ≤ 3 * A)
    (hx : ∀ z ∈ D, root z ≠ zero ∧ root z *ᵍ root z = z)
    (hfar : ∀ P : List K, P.length ≤ 2*k →
      (D.filter (fun z => decide (RoundPoly.evalCoeffs P (root z) = pos z ∧
        RoundPoly.evalCoeffs P (neg (root z)) = negVal z))).length < A) :
    qsum (2^(hi+400)) (fun c => if (foldCandidates D k A root pos negVal (whirField c.val 0)).isEmpty
      then 0 else 1) ≤ 2^hi * (max 1 D.length * (2^400 / quinticGoldilocksCard + 1)) := by
  apply foldRound_exception_mass hi D k A root pos negVal hd hk hA hTriple
  intro E O hE hO
  apply Nat.lt_of_le_of_lt _ (hfar (interleavePoly E O) (interleavePoly_length_le k E O hE hO))
  apply nodup_length_le_of_subset (List.Pairwise.filter _ hd)
  intro z hz
  obtain ⟨hm, h⟩ := List.mem_filter.mp hz
  obtain ⟨he, ho⟩ := of_decide_eq_true h
  obtain ⟨hn, hs⟩ := hx z hm
  exact List.mem_filter.mpr ⟨hm, decide_eq_true (interleave_recovers_pair E O _ _ _ hn
    (by rw [hs]; exact he) (by rw [hs]; exact ho))⟩

/-- A fold prefix survives when the decoded polynomial agrees with the residual
    quadratic message at the sampled challenge. -/
def foldClaimLive (D : List K) (k A : Nat) (root pos negVal : K → K)
    (terms : List (K × K)) (msg : List K) (t : K) : Bool :=
  (foldCandidates D k A root pos negVal t).any (fun p =>
    decide (RoundPoly.evalCoeffs msg t = kernelValue p.coeffs (terms.map (foldKernelTerm t))))

/-- Complete binary fold transition estimate. A false input claim admits at most
    max(2,n) live challenges, including both the distance and the sumcheck cases. -/
theorem foldClaimLive_seed_bound (hi : Nat) (D : List K) (k A : Nat) (root pos negVal : K → K)
    (hd : D.Nodup) (hk : 0 < k) (hA : k ≤ A) (hOverlap : D.length+k ≤ 2*A)
    (hTriple : 2*D.length+k ≤ 3*A) (hx : ∀ z ∈ D, root z ≠ zero ∧ root z *ᵍ root z = z)
    (terms : List (K × K)) (msg : List K) (hlen : msg.length ≤ 3)
    (hFalse : ∀ P : List K, P.length ≤ 2*k →
      A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs P (root z) = pos z ∧
        RoundPoly.evalCoeffs P (neg (root z)) = negVal z))).length →
      RoundPoly.evalCoeffs msg zero +ᵍ RoundPoly.evalCoeffs msg one ≠ kernelValue P terms) :
    qsum (2^(hi+400)) (fun c => if foldClaimLive D k A root pos negVal terms msg (whirField c.val 0)
      then 1 else 0) ≤ 2^hi * (max 2 D.length * (2^400 / quinticGoldilocksCard + 1)) := by
  apply whirField_predicate_mass
  intro S hs hit
  let C := foldCandidates D k A root pos negVal
  let pred := fun (t : K) (p : GsUniPoly K) =>
    decide (RoundPoly.evalCoeffs msg t = kernelValue p.coeffs (terms.map (foldKernelTerm t)))
  let Q := fun t => ((C t).find? (pred t)).elim [] (fun p => p.coeffs)
  have witness (t : K) (ht : t ∈ S) : ∃ p ∈ C t, pred t p = true ∧ Q t = p.coeffs := by
    have ha : (C t).any (pred t) = true := hit t ht
    cases hf : (C t).find? (pred t) with
    | none =>
      obtain ⟨p,hm,hp⟩ := List.any_eq_true.mp ha
      exact absurd hp (List.find?_eq_none.mp hf p hm)
    | some p => exact ⟨p, List.mem_of_find?_eq_some hf, List.find?_some hf, by simp [Q,hf]⟩
  apply Nat.le_of_not_gt
  intro hbig
  have far := quinticFold_exceptional_challenges D S k A root pos negVal Q hd hs hk hTriple (by
    intro t ht
    obtain ⟨p,hm,_,he⟩ := witness t ht
    have spec := (mem_gsDecodeList_iff _ hd (d := k-1) (A := A) (by omega) p).mp hm
    rw [he]; exact ⟨by have := spec.1; omega, spec.2⟩) (by
    intro E O hE hO
    apply Nat.lt_of_not_ge
    intro hj
    let P := interleavePoly E O
    have len := interleavePoly_length_le k E O hE hO
    have near : A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs P (root z) = pos z ∧
        RoundPoly.evalCoeffs P (neg (root z)) = negVal z))).length := by
      apply Nat.le_trans hj
      apply nodup_length_le_of_subset (List.Pairwise.filter _ hd)
      intro z hz
      obtain ⟨hm, h⟩ := List.mem_filter.mp hz
      obtain ⟨he, ho⟩ := of_decide_eq_true h
      obtain ⟨hn, hs⟩ := hx z hm
      exact List.mem_filter.mpr ⟨hm, decide_eq_true (interleave_recovers_pair E O _ _ _ hn
        (by rw [hs]; exact he) (by rw [hs]; exact ho))⟩
    have few := close_fold_wrong_claim D k A root pos negVal hd hk hA hOverlap hx P len near terms msg S hs
      hlen (hFalse P len near) (fun t ht => by
        obtain ⟨p,hm,hp,_⟩ := witness t ht; exact ⟨p,hm,of_decide_eq_true hp⟩)
    omega)
  omega

def stageDomain (s : Nat) : List K := (List.range (2^s)).map (cosetPoint s)

theorem stageDomain_nodup (s : Nat) (hs : s ≤ 32) : (stageDomain s).Nodup := by
  rw [stageDomain, cosetPoint_table]
  apply List.pairwise_map.mpr
  exact (ZkHemV2.twoAdicCoset_nodup s hs).imp (fun hn he => hn (QuinticGoldilocks.ofBase_injective he))

private theorem domain_at (s j : Nat) (hj : j < 2^s) :
    (stageDomain s)[j]'(by simpa [stageDomain] using hj) = cosetPoint s j := by
  simp only [stageDomain, List.getElem_map, List.getElem_range]

private theorem coord_index (s j : Nat) (hs : s ≤ 32) (hj : j < 2^s) :
    (stageDomain s).idxOf (cosetPoint s j) = j := by
  rw [← domain_at s j hj]
  exact (stageDomain_nodup s hs).idxOf_getElem j _

def pairRoot (s : Nat) (z : K) : K := cosetPoint (s+1) ((stageDomain s).idxOf z)

private theorem pairRoot_spec (s : Nat) (hs : s+1 ≤ 32) (z : K) (hz : z ∈ stageDomain s) :
    pairRoot s z ≠ zero ∧ pairRoot s z *ᵍ pairRoot s z = z := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
  have h := List.mem_range.mp hj
  simp only [pairRoot, coord_index s j (by omega) h]
  refine ⟨cosetPoint_ne_zero _ _ hs, ?_⟩
  simpa only [ZkHemV2.pow2Iter_one, Nat.add_comm 1 s] using cosetPoint_folded 1 s j (by omega)

private theorem cosetPoint_opposite (s j : Nat) (hs : s+1 ≤ 32) :
    cosetPoint (s+1) (2^s + j) = neg (cosetPoint (s+1) j) := by
  simpa only [fiberPoint, LawfulCommRing.one_mul] using fiberPoint_antipode s j hs one

def pairPos (s : Nat) (table : List K) (z : K) := table.getD ((stageDomain s).idxOf z) zero
def pairNeg (s : Nat) (table : List K) (z : K) := table.getD (2^s + (stageDomain s).idxOf z) zero

def wordLive (D : List K) (k A : Nat) (word : K → K) (terms : List (K × K)) (cl : K) : Bool :=
  (gsDecodeList (k-1) A D word).any (fun p => decide (kernelValue p.coeffs terms = cl))

theorem wordLive_iff (D : List K) (k A : Nat) (word : K → K) (terms : List (K × K)) (cl : K)
    (hd : D.Nodup) (hk : 0 < k) (hA : k ≤ A) :
    wordLive D k A word terms cl = true ↔ ∃ P : List K, P.length ≤ k ∧
      A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs P z = word z))).length ∧ kernelValue P terms = cl := by
  rw [wordLive, List.any_eq_true]
  have len : k-1+1 = k := by omega
  constructor
  · rintro ⟨p,hm,hp⟩
    have h := (mem_gsDecodeList_iff word hd (d := k-1) (A := A) (by omega) p).mp hm
    rw [len] at h
    exact ⟨_, h.1, h.2, of_decide_eq_true hp⟩
  · rintro ⟨P,hp,hc,he⟩
    let p := UPoly.ofList P
    have eval (z : K) : RoundPoly.evalCoeffs p.coeffs z = RoundPoly.evalCoeffs P z := by
      rw [show p.coeffs = trimPoly P from UPoly.coeffs_ofList P, evalCoeffs_trimPoly]
    refine ⟨p, (mem_gsDecodeList_iff word hd (d := k-1) (A := A) (by omega) p).mpr ⟨?_,?_⟩,
      decide_eq_true ((kernelValue_congr eval terms).trans he)⟩
    · rw [len, show p.coeffs = trimPoly P from UPoly.coeffs_ofList P]
      exact Nat.le_trans (trimPoly_length_le P) hp
    · simpa only [eval] using hc

theorem close_word_candidate_unique (D : List K) (k A : Nat) (word : K → K)
    (hd : D.Nodup) (hk : 0 < k) (hA : k ≤ A) (hOverlap : D.length+k ≤ 2*A)
    {P Q : GsUniPoly K} (hp : P ∈ gsDecodeList (k-1) A D word) (hq : Q ∈ gsDecodeList (k-1) A D word) :
    P = Q := by
  have spec := fun R => (mem_gsDecodeList_iff word hd (d := k-1) (A := A) (by omega) R).mp
  let hit := fun (R : GsUniPoly K) z => decide (RoundPoly.evalCoeffs R.coeffs z = word z)
  have p := spec P hp
  have q := spec Q hq
  have ph : A ≤ (D.filter (hit P)).length := p.2
  have qh : A ≤ (D.filter (hit Q)).length := q.2
  have overlap := filter_overlap_len (hit P) (hit Q) D
  have eq := trimPoly_eq_of_agree_on_nodup p.1 q.1 (U := D.filter fun z => hit P z && hit Q z)
    (List.Pairwise.filter _ hd) (by omega) (fun z hz => by
      obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp (List.mem_filter.mp hz).2
      exact (of_decide_eq_true a).trans (of_decide_eq_true b).symm)
  exact UPoly.ext (P.trimmed.symm.trans (eq.trans Q.trimmed))

private theorem scalar_agreement (s : Nat) (hs : s ≤ 32) (P table : List K) :
    ((stageDomain s).filter (fun z => decide (RoundPoly.evalCoeffs P z = pairPos s table z))).length =
    ((List.range (2^s)).filter (fun j => decide (RoundPoly.evalCoeffs P (cosetPoint s j) = table.getD j zero))).length := by
  rw [stageDomain, List.filter_map, List.length_map]
  apply congrArg List.length
  apply List.filter_congr
  intro j hj
  simp only [Function.comp_apply, pairPos, coord_index _ _ hs (List.mem_range.mp hj)]

private theorem false_word_agrees (s k A : Nat) (hs : s ≤ 32) (hk : 0 < k) (hA : k ≤ A)
    (prev : K → K) (terms : List (K × K)) (cl : K) (P : List K) (hp : P.length ≤ k)
    (hFalse : wordLive (stageDomain s) k A prev terms cl = false) :
    qsum (2^s) (fun i => if cl = kernelValue P terms ∧
      prev (cosetPoint s i.val) = RoundPoly.evalCoeffs P (cosetPoint s i.val) then 1 else 0) ≤ A := by
  by_cases hcl : cl = kernelValue P terms
  · have far : ((stageDomain s).filter (fun z => decide (RoundPoly.evalCoeffs P z = prev z))).length < A := by
      apply Nat.lt_of_not_ge
      intro hn
      have live := (wordLive_iff _ _ _ _ _ _ (stageDomain_nodup s hs) hk hA).mpr ⟨P,hp,hn,hcl.symm⟩
      rw [hFalse] at live; contradiction
    rw [stageDomain, List.filter_map, List.length_map, filter_range_length_qsum] at far
    apply Nat.le_trans (Nat.le_of_eq (qsum_congr (g := fun i =>
      if RoundPoly.evalCoeffs P (cosetPoint s i.val) = prev (cosetPoint s i.val) then 1 else 0)
      (fun i => by
        by_cases h : prev (cosetPoint s i.val) = RoundPoly.evalCoeffs P (cosetPoint s i.val)
        · simp [hcl,h]
        · simp [hcl,h,Ne.symm h])))
    simpa only [Function.comp_apply, decide_eq_true_eq] using Nat.le_of_lt far
  · simp only [hcl, false_and, ↓reduceIte, qsum_const, Nat.mul_zero, Nat.zero_le]

def shiftTableLive (s t k A : Nat) (next prev : K → K) (terms : List (K × K)) (cl : K)
    (zs ys : List K) (u : Nat) (γ : K) : Bool :=
  let qs := shiftPositions s t u
  wordLive (stageDomain s) k A next
    (terms ++ weightedPoints γ (zs ++ qs.map (cosetPoint s)))
    (combineClaim cl γ (ys ++ qs.map (fun j => prev (cosetPoint s j))))

/-- The nonterminal answer-round flip bound. The newly committed oracle picks at
    most one close polynomial before the answer challenge, so the positional
    error is counted once. No hypothesis on the committed table contents. -/
theorem shiftTableLive_mass (s t k A : Nat) (hs : s ≤ 32) (hk : 0 < k) (hA : k ≤ A)
    (hov : 2^s+k ≤ 2*A) (next prev : K → K) (terms : List (K × K)) (cl : K)
    (zs ys : List K) (hlen : ys.length = zs.length)
    (hFalse : wordLive (stageDomain s) k A prev terms cl = false) :
    qsum ((2^32)^t * 2^2000) (fun c => if shiftTableLive s t k A next prev terms cl zs ys
      (c.val/2^2000) (whirField c.val 0) then 1 else 0) ≤
      (2^(32-s)*A)^t * 2^2000 + (2^32)^t * (2^1600 * ((zs.length+t) * (2^400/quinticGoldilocksCard+1))) := by
  let D := stageDomain s
  let C := gsDecodeList (k-1) A D next
  have hd := stageDomain_nodup s hs
  cases hc : C with
  | nil =>
    have no (u : Nat) (γ : K) : shiftTableLive s t k A next prev terms cl zs ys u γ = false := by
      unfold shiftTableLive wordLive
      change C.any _ = false
      rw [hc]; rfl
    simp only [no, Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero, Nat.zero_le]
  | cons p rest =>
    have hm : p ∈ C := hc ▸ List.mem_cons_self
    have deg := ((mem_gsDecodeList_iff next hd (d := k-1) (A := A) (by omega) p).mp hm).1
    have size : D.length = 2^s := by simp [D,stageDomain]
    let reads := fun j => prev (cosetPoint s j)
    have he (u : Nat) (γ : K) (ha : shiftTableLive s t k A next prev terms cl zs ys u γ = true) :
        shiftBatchLive s t u p.coeffs terms cl zs ys reads γ = true := by
      obtain ⟨q,hq,hv⟩ := List.any_eq_true.mp ha
      have eq := close_word_candidate_unique D k A next hd hk hA (size ▸ hov) hq hm
      subst q
      exact decide_eq_true (of_decide_eq_true hv).symm
    have upper := shiftBatchLive_mass s t A hs p.coeffs terms cl zs ys reads hlen
      (false_word_agrees s k A hs hk hA prev terms cl _ (by omega) hFalse)
    apply Nat.le_trans (qsum_le_qsum (g := fun c => if shiftBatchLive s t (c.val/2^2000) p.coeffs terms cl zs ys reads
      (whirField c.val 0) then 1 else 0) ?_) upper
    intro c
    split
    · rename_i ha; rw [he _ _ ha]; decide
    · exact Nat.zero_le _

/-- A agreeing antipodal pairs of the real table give 2A scalar agreements
    in the original WHIR language. -/
theorem pair_agreement_to_scalar (s A : Nat) (hs : s+1 ≤ 32) (table P : List K)
    (hc : A ≤ ((stageDomain s).filter (fun z => decide
      (RoundPoly.evalCoeffs P (pairRoot s z) = pairPos s table z ∧
       RoundPoly.evalCoeffs P (neg (pairRoot s z)) = pairNeg s table z))).length) :
    2*A ≤ ((List.range (2^(s+1))).filter (fun j => decide
      (RoundPoly.evalCoeffs P (cosetPoint (s+1) j) = table.getD j zero))).length := by
  let good := fun j => decide (RoundPoly.evalCoeffs P (cosetPoint (s+1) j) = table.getD j zero)
  let both := fun z => decide (RoundPoly.evalCoeffs P (pairRoot s z) = pairPos s table z ∧
       RoundPoly.evalCoeffs P (neg (pairRoot s z)) = pairNeg s table z)
  let L := List.range (2^s)
  change A ≤ ((L.map (cosetPoint s)).filter both).length at hc
  rw [List.filter_map, List.length_map] at hc
  have subset (j : Nat) (hj : j ∈ L.filter (both ∘ cosetPoint s)) :
      j ∈ L ∧ good j = true ∧ good (2^s+j) = true := by
    obtain ⟨hm,hb⟩ := List.mem_filter.mp hj
    have idx := coord_index s j (by omega) (List.mem_range.mp hm)
    change decide (_ ∧ _) = true at hb
    obtain ⟨hp,hn⟩ := of_decide_eq_true hb
    dsimp only [pairRoot, pairPos, pairNeg] at hp hn
    rw [idx] at hp hn
    exact ⟨hm, decide_eq_true hp, decide_eq_true (by rw [cosetPoint_opposite s j hs]; exact hn)⟩
  have nd : (L.filter (both ∘ cosetPoint s)).Nodup := List.Pairwise.filter _ (Constructive.nodup_range _)
  have lo := nodup_length_le_of_subset (M := L.filter good) nd (fun j h =>
    List.mem_filter.mpr ⟨(subset j h).1, (subset j h).2.1⟩)
  have hi := nodup_length_le_of_subset (M := L.filter (good ∘ (fun j => 2^s+j))) nd (fun j h =>
    List.mem_filter.mpr ⟨(subset j h).1, (subset j h).2.2⟩)
  change 2*A ≤ ((List.range (2^(s+1))).filter good).length
  rw [Nat.pow_succ', Nat.two_mul (2^s), List.range_add, List.filter_append, List.length_append,
    List.filter_map, List.length_map]
  change 2*A ≤ (L.filter good).length + (L.filter (good ∘ (fun j => 2^s+j))).length
  omega

/-- The same fold flip bound holds at subsequent input tables after the previous
    shift round has installed a new claim and kernel. -/
theorem table_fold_flip (s k A : Nat) (hs : s+1 ≤ 32) (hk : 0 < k) (hA : k ≤ A)
    (hOverlap : 2^s+k ≤ 2*A) (hTriple : 2*2^s+k ≤ 3*A) (table msg : List K)
    (terms : List (K × K)) (cl : K) (hlen : msg.length ≤ 3)
    (hclaim : RoundPoly.evalCoeffs msg zero +ᵍ RoundPoly.evalCoeffs msg one = cl)
    (hfalse : wordLive (stageDomain (s+1)) (2*k) (2*A) (pairPos (s+1) table) terms cl = false) :
    qsum (2^22480) (fun c => if foldClaimLive (stageDomain s) k A (pairRoot s)
      (pairPos s table) (pairNeg s table) terms msg (whirField c.val 0) then 1 else 0) ≤
      2^22080 * (max 2 (2^s) * (2^400/quinticGoldilocksCard+1)) := by
  have n : (stageDomain s).length = 2^s := by simp [stageDomain]
  have h := foldClaimLive_seed_bound 22080 (stageDomain s) k A (pairRoot s) (pairPos s table) (pairNeg s table)
    (stageDomain_nodup s (by omega)) hk hA (n ▸ hOverlap) (n ▸ hTriple)
    (pairRoot_spec s hs) terms msg hlen (fun P hp hc hbad => by
      have h := (wordLive_iff (stageDomain (s+1)) (2*k) (2*A) (pairPos (s+1) table) terms cl
        (stageDomain_nodup (s+1) hs) (by omega) (by omega)).mpr
        ⟨P,hp, by rw [scalar_agreement _ hs]; exact pair_agreement_to_scalar s A hs table P hc,
          hbad.symm.trans hclaim⟩
      rw [hfalse] at h; contradiction)
  simpa only [n] using h

/-- The stage-zero flip estimate on arbitrary 256-point statements outside the
    actual WHIR language, for any valid first sumcheck message. -/
theorem multiStage_first_fold_flip (x : WhirStmt K)
    (hx : ¬ whirInLang zkHemV2MultiStageEnv zkHemV2MultiStageSched x)
    (msg : List K) (hlen : msg.length ≤ 3)
    (hclaim : RoundPoly.evalCoeffs msg zero +ᵍ RoundPoly.evalCoeffs msg one = x.claim) :
    qsum (2^22480) (fun c => if foldClaimLive (stageDomain 7) 8 88 (pairRoot 7)
      (pairPos 7 x.table) (pairNeg 7 x.table) [(one,one)] msg (whirField c.val 0)
      then 1 else 0) ≤ 2^22080 * (128 * (2^400 / quinticGoldilocksCard + 1)) := by
  have n : (stageDomain 7).length = 128 := by simp [stageDomain]
  have h := foldClaimLive_seed_bound 22080 (stageDomain 7) 8 88 (pairRoot 7)
    (pairPos 7 x.table) (pairNeg 7 x.table) (stageDomain_nodup 7 (by decide))
    (by decide) (by decide) (by rw [n]; decide) (by rw [n]; decide)
    (pairRoot_spec 7 (by decide)) [(one,one)] msg hlen (by
      intro P hp hc he
      apply hx
      refine ⟨P, ?_, pair_agreement_to_scalar 7 88 (by decide) _ _ hc, ?_⟩
      · change P.length ≤ 17; omega
      · change RoundPoly.evalCoeffs P one = x.claim
        rw [← hclaim, he]
        simp only [kernelValue, LawfulCommRing.one_mul, LawfulCommRing.add_zero])
  simpa only [n, show max 2 128 = 128 by decide] using h

theorem multiStage_fold_budget (st : WhirStage) (h : st ∈ zkHemV2MultiStageSched.stages) :
    RatBound.le ⟨2^22080 * (128 * (2^400 / quinticGoldilocksCard + 1)),
      2^22480, Nat.two_pow_pos _⟩ (st.foldBound quinticGoldilocksCard quinticGoldilocksCard_pos) := by
  simp only [zkHemV2MultiStageSched, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> rw [WhirStage.foldBound_eq] <;> decide +kernel

/-- The terminal polynomial is fixed in the commit round. A successful terminal
    check supplies both the carried claim and all sampled scalar evaluations. -/
def terminalLive (s t : Nat) (prev : K → K) (terms : List (K × K)) (cl : K) (P : List K) (c : Nat) : Bool :=
  (List.range t).all (fun j =>
    let z := cosetPoint s (whirPosition c j (2^s))
    decide (cl = kernelValue P terms ∧ prev z = RoundPoly.evalCoeffs P z))

theorem terminalLive_mass (s t k A : Nat) (hs : s ≤ 32) (hk : 0 < k) (hA : k ≤ A)
    (prev : K → K) (terms : List (K × K)) (cl : K) (P : List K) (hp : P.length ≤ k)
    (hFalse : wordLive (stageDomain s) k A prev terms cl = false) :
    qsum ((2^32)^t * 2^2000) (fun c => if terminalLive s t prev terms cl P c.val then 1 else 0) ≤
      (2^(32-s)*A)^t * 2^2000 := by
  let good := fun j => decide (cl = kernelValue P terms ∧ prev (cosetPoint s j) = RoundPoly.evalCoeffs P (cosetPoint s j))
  exact whirPosition_all_good_seeds s t A hs good (by
    simpa only [good, decide_eq_true_eq] using false_word_agrees s k A hs hk hA prev terms cl P hp hFalse)

def multiStageFoldBad : Nat := 2^22080 * (128 * (2^400 / quinticGoldilocksCard + 1))

def multiStageShiftBad : Nat := (2^25*88)^640 * 2^2000 +
  (2^32)^640 * (2^1600 * (641 * (2^400/quinticGoldilocksCard+1)))

theorem multiStage_shift_budget (st : WhirStage) (h : st ∈ zkHemV2MultiStageSched.stages) :
    RatBound.le ⟨multiStageShiftBad, 2^22480, Nat.two_pow_pos _⟩
      (st.shiftBound quinticGoldilocksCard quinticGoldilocksCard_pos) := by
  simp only [zkHemV2MultiStageSched, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> rw [WhirStage.shiftBound_eq] <;> unfold multiStageShiftBad <;> decide +kernel

/-! ## Round-by-round state for the 256-point schedule -/

private inductive CertStage where | first | middle | last
private def CertStage.log : CertStage → Nat | .first => 7 | .middle => 6 | .last => 5
private def CertStage.coeffs : CertStage → Nat | .first => 8 | .middle => 4 | .last => 2
private def CertStage.threshold : CertStage → Nat | .first => 88 | .middle => 44 | .last => 22

private structure CertInput where
  table : List K
  terms : List (K × K)
  claim : K

private structure CertFold where
  word : K → K
  terms : List (K × K)
  claim : K

private abbrev Round := WhirMsg K × Nat

private def validRound (i : CertInput) (m : WhirMsg K) : Bool :=
  decide (m.poly.length ≤ 3 ∧ RoundPoly.evalCoeffs m.poly zero +ᵍ RoundPoly.evalCoeffs m.poly one = i.claim)

private def makeFold (st : CertStage) (i : CertInput) (r : Round) : CertFold :=
  let α := whirField r.2 0
  ⟨fun z => quinticWhirFold2 (pairRoot st.log z) α (pairPos st.log i.table z) (pairNeg st.log i.table z),
    i.terms.map (foldKernelTerm α), RoundPoly.evalCoeffs r.1.poly α⟩

private def inputLive (st : CertStage) (i : CertInput) :=
  wordLive (stageDomain (st.log+1)) (2*st.coeffs) (2*st.threshold) (pairPos (st.log+1) i.table) i.terms i.claim

private def foldedLive (st : CertStage) (f : CertFold) :=
  wordLive (stageDomain st.log) st.coeffs st.threshold f.word f.terms f.claim

private theorem foldedLive_eq (st : CertStage) (i : CertInput) (r : Round) :
    foldedLive st (makeFold st i r) =
      foldClaimLive (stageDomain st.log) st.coeffs st.threshold (pairRoot st.log)
        (pairPos st.log i.table) (pairNeg st.log i.table) i.terms r.1.poly (whirField r.2 0) := by
  unfold foldedLive wordLive makeFold foldClaimLive foldCandidates
  dsimp only
  congr 1
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]; exact eq_comm

private def makeShift (st : CertStage) (f : CertFold) (cm an : Round) : CertInput :=
  let pts := (shiftPositions st.log 640 (an.2/2^2000)).map (cosetPoint st.log)
  let γ := whirField an.2 0
  ⟨cm.1.table, f.terms ++ weightedPoints γ ([whirField cm.2 0] ++ pts),
    combineClaim f.claim γ (an.1.answers ++ pts.map f.word)⟩

private inductive CertPhase where
  | input (st : CertStage) (i : CertInput)
  | fold (st : CertStage) (f : CertFold)
  | commit (st : CertStage) (f : CertFold) (cm : Round)
  | done (ok : Bool)
  | dead

private def CertPhase.live : CertPhase → Bool
  | .input st i => inputLive st i
  | .fold st f | .commit st f _ => foldedLive st f
  | .done ok => ok
  | .dead => false

private def certStart (x : WhirStmt K) : CertPhase := .input .first ⟨x.table,[(one,one)],x.claim⟩

private def certStep : CertPhase → Round → CertPhase
  | .input st i, r => if validRound i r.1 then .fold st (makeFold st i r) else .dead
  | .fold st f, r => .commit st f r
  | .commit st f cm, an =>
    if an.1.answers.length = 1 then
      match st with
      | .first => .input .middle (makeShift .first f cm an)
      | .middle => .input .last (makeShift .middle f cm an)
      | .last => .done (decide (cm.1.poly.length ≤ 2) && terminalLive 5 640 f.word f.terms f.claim cm.1.poly an.2)
    else .dead
  | _, _ => .dead

private def certBudget (r : Nat) : Nat :=
  match r % 3 with
  | 0 => multiStageFoldBad
  | 1 => 0
  | _ => multiStageShiftBad

private def CertPhase.atRound (r : Nat) : CertPhase → Prop
  | .input .. => r%3 = 0
  | .fold .. => r%3 = 1
  | .commit .. => r%3 = 2
  | _ => True

private theorem certRound_step (r : Nat) (p : CertPhase) (m : Round) (hp : p.atRound r) :
    (certStep p m).atRound (r+1) := by
  cases p with
  | input st i =>
    change r%3 = 0 at hp
    simp only [certStep]; split
    · change (r+1)%3 = 1; omega
    · trivial
  | fold st f =>
    change r%3 = 1 at hp
    change (r+1)%3 = 2; omega
  | commit st f cm =>
    change r%3 = 2 at hp
    simp only [certStep]; split
    · cases st with
      | first | middle => change (r+1)%3 = 0; omega
      | last => trivial
    · trivial
  | dead | done => trivial

private theorem certRound_run (r : Nat) (p : CertPhase) (tr : List Round) (hp : p.atRound r) :
    (tr.foldl certStep p).atRound (r+tr.length) := by
  induction tr generalizing r p with
  | nil => exact hp
  | cons m tr ih =>
    simpa only [List.foldl_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1]
      using ih (r+1) (certStep p m) (certRound_step r p m hp)

private theorem certStart_false (x : WhirStmt K) (hx : ¬ whirInLang zkHemV2MultiStageEnv zkHemV2MultiStageSched x) :
    (certStart x).live = false := by
  cases h : (certStart x).live with
  | false => rfl
  | true =>
    change wordLive (stageDomain 8) 16 176 (pairPos 8 x.table) [(one,one)] x.claim = true at h
    obtain ⟨P,hp,hc,he⟩ := (wordLive_iff _ _ _ _ _ _ (stageDomain_nodup 8 (by decide)) (by decide) (by decide)).mp h
    apply False.elim; apply hx
    refine ⟨P, ?_, ?_, ?_⟩
    · change P.length ≤ 17; omega
    · rw [scalar_agreement 8 (by decide)] at hc
      exact hc
    · change RoundPoly.evalCoeffs P one = x.claim
      simpa only [kernelValue, LawfulCommRing.one_mul, LawfulCommRing.add_zero] using he

private theorem certStage_geom (st : CertStage) : st.log+1 ≤ 32 ∧ 0 < st.coeffs ∧
    st.coeffs ≤ st.threshold ∧ 2^st.log+st.coeffs ≤ 2*st.threshold ∧
    2*2^st.log+st.coeffs ≤ 3*st.threshold ∧ max 2 (2^st.log) ≤ 128 := by
  cases st <;> decide

private theorem certInput_flip (st : CertStage) (i : CertInput) (m : WhirMsg K) (hp : inputLive st i = false) :
    qsum (2^22480) (fun c => if (certStep (.input st i) (m,c.val)).live then 1 else 0) ≤ multiStageFoldBad := by
  cases hm : validRound i m with
  | false => simp only [certStep, hm, Bool.false_eq_true, ↓reduceIte, CertPhase.live, qsum_const, Nat.mul_zero, Nat.zero_le]
  | true =>
    obtain ⟨hlen, he⟩ := of_decide_eq_true hm
    obtain ⟨hs,hk,hA,hov,hTriple,hmax⟩ := certStage_geom st
    simp only [certStep, hm, ↓reduceIte, CertPhase.live, foldedLive_eq]
    apply Nat.le_trans (table_fold_flip _ _ _ hs hk hA hov hTriple i.table m.poly i.terms i.claim hlen he hp)
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmax)

private theorem certShift_budget_eq (st : CertStage) :
    (2^(32-st.log)*st.threshold)^640*2^2000 +
      (2^32)^640*(2^1600*(641*(2^400/quinticGoldilocksCard+1))) = multiStageShiftBad := by
  cases st <;> rfl

private theorem shift_live_eq (st st' : CertStage) (f : CertFold) (cm an : Round)
    (hlog : st'.log+1 = st.log) (hk : 2*st'.coeffs = st.coeffs) (ha : 2*st'.threshold = st.threshold) :
    inputLive st' (makeShift st f cm an) =
      shiftTableLive st.log 640 st.coeffs st.threshold (pairPos st.log cm.1.table) f.word f.terms f.claim
        [whirField cm.2 0] an.1.answers (an.2/2^2000) (whirField an.2 0) := by
  simp only [inputLive, makeShift, shiftTableLive, hlog,hk,ha,List.map_map,Function.comp_def]

private theorem certCommit_flip (st : CertStage) (f : CertFold) (cm : Round) (m : WhirMsg K)
    (hp : foldedLive st f = false) :
    qsum (2^22480) (fun c => if (certStep (.commit st f cm) (m,c.val)).live then 1 else 0) ≤ multiStageShiftBad := by
  by_cases hy : m.answers.length = 1
  · obtain ⟨hs,hk,hA,hov,_,_⟩ := certStage_geom st
    have count (st' : CertStage) (hl : st'.log+1 = st.log) (hd : 2*st'.coeffs = st.coeffs)
        (ha : 2*st'.threshold = st.threshold) :
        qsum (2^22480) (fun c => if inputLive st' (makeShift st f cm (m,c.val)) then 1 else 0) ≤ multiStageShiftBad := by
      simp only [shift_live_eq st st' f cm _ hl hd ha]
      rw [← certShift_budget_eq st]
      exact shiftTableLive_mass st.log 640 st.coeffs st.threshold (by omega) hk hA hov _ f.word f.terms f.claim
        [whirField cm.2 0] m.answers hy hp
    cases st with
    | first => simpa only [certStep,hy,↓reduceIte,CertPhase.live] using count .middle rfl rfl rfl
    | middle => simpa only [certStep,hy,↓reduceIte,CertPhase.live] using count .last rfl rfl rfl
    | last =>
      by_cases hd : cm.1.poly.length ≤ 2
      · simp only [certStep,hy,↓reduceIte,CertPhase.live,hd,decide_true,Bool.true_and]
        have h := terminalLive_mass 5 640 2 22 (by decide) (by decide) (by decide) f.word f.terms f.claim cm.1.poly hd hp
        apply Nat.le_trans h
        rw [← certShift_budget_eq .last]
        exact Nat.le_add_right _ _
      · simp only [certStep,hy,↓reduceIte,CertPhase.live,hd,decide_false,Bool.false_and,Bool.false_eq_true,
          qsum_const,Nat.mul_zero,Nat.zero_le]
  · simp only [certStep,hy,↓reduceIte,CertPhase.live,Bool.false_eq_true,qsum_const,Nat.mul_zero,Nat.zero_le]

private theorem certPhase_flip (p : CertPhase) (r : Nat) (hr : p.atRound r) (hp : p.live = false) (m : WhirMsg K) :
    qsum (2^22480) (fun c => if (certStep p (m,c.val)).live then 1 else 0) ≤ certBudget r := by
  cases p with
  | input st i => change r%3=0 at hr; rw [certBudget,hr]; exact certInput_flip st i m hp
  | fold st f =>
    change r%3=1 at hr
    change foldedLive st f = false at hp
    simp only [certStep,CertPhase.live,hp,Bool.false_eq_true,↓reduceIte,qsum_const,Nat.mul_zero,Nat.zero_le]
  | commit st f cm => change r%3=2 at hr; rw [certBudget,hr]; exact certCommit_flip st f cm m hp
  | dead | done => simp only [certStep,CertPhase.live,Bool.false_eq_true,↓reduceIte,qsum_const,Nat.mul_zero,Nat.zero_le]

/-! ## Nonconstant acceptance and OOD mutation -/

def embedNat (n : Nat) : K := QuinticGoldilocks.ofBase (Goldilocks.ofNat n)

def examplePoly : List K := [one, embedNat 2, embedNat 3, zero, zero, one]

def exampleTable (k : Nat) (P : List K) : List K :=
  (List.range (2 ^ k)).map fun j => RoundPoly.evalCoeffs P (cosetPoint k j)

def exampleStmt : WhirStmt K := ⟨exampleTable 8 examplePoly, RoundPoly.evalCoeffs examplePoly one⟩

/-- Fold challenges are one, OOD points are two, and the answer challenge samples index zero.
    The committed tables are evaluations of the first and second folded polynomials. -/
def exampleTranscript (lastAnswer : K) : List (WhirMsg K × Nat) :=
  let p1 := foldPolyCoeffs one examplePoly
  let p2 := foldPolyCoeffs one p1
  let p3 := foldPolyCoeffs one p2
  [(⟨[], [zero, embedNat 4, embedNat 3], []⟩, 1),
   (⟨exampleTable 7 p1, [], []⟩, 2), (⟨[], [], [RoundPoly.evalCoeffs p1 (embedNat 2)]⟩, 0),
   (⟨[], [zero, embedNat 4, embedNat 3], []⟩, 1),
   (⟨exampleTable 6 p2, [], []⟩, 2), (⟨[], [], [RoundPoly.evalCoeffs p2 (embedNat 2)]⟩, 0),
   (⟨[], [zero, embedNat 6, one], []⟩, 1),
   (⟨[], p3, []⟩, 2), (⟨[], [], [lastAnswer]⟩, 0)]

theorem example_all_three_odd_parts :
    [examplePoly, foldPolyCoeffs one examplePoly,
     foldPolyCoeffs one (foldPolyCoeffs one examplePoly)].all
      (fun p => decide (foldPolyCoeffs zero p ≠ foldPolyCoeffs one p)) = true := by
  decide +kernel

private theorem combineClaim_zero (c : K) (vs : List K) : combineClaim c zero vs = c := by
  rw [combineClaim.public_eq_1]
  suffices ∀ (l : List K), l.foldl (fun (acc : K × K) v =>
      (acc.1 +ᵍ acc.2 *ᵍ v, acc.2 *ᵍ zero)) (c, zero) = (c, zero) by rw [this]
  intro l
  induction l with
  | nil => rfl
  | cons v l ih => simpa only [List.foldl_cons, LawfulCommRing.zero_mul,
      LawfulCommRing.add_zero] using ih

private theorem whirField_small (n : Nat) (hn : n < 8) :
    whirField n 0 = embedNat n := by
  have he : encodeQuinticNat (embedNat n) = n := by
    have hlt : n < goldilocksPrime := Nat.lt_trans hn (by decide)
    rw [encodeQuinticNat.public_eq_1]
    simp only [embedNat, QuinticGoldilocks.ofBase, Goldilocks.ofNat, Nat.mod_eq_of_lt hlt]
    change n + goldilocksPrime * (0 + goldilocksPrime * (0 + goldilocksPrime * (0 + goldilocksPrime * 0))) = n
    simp
  unfold whirField
  rw [show 400 * (0 % 5) = 0 by decide, Nat.shiftRight_zero, Nat.mod_eq_of_lt
    (Nat.lt_trans hn (by decide : 8 < 2 ^ 400))]
  rw [decodeQuintic400.public_eq_1, Nat.mod_eq_of_lt (Nat.lt_trans hn (by decide : 8 < quinticGoldilocksCard)),
    ← he, decodeQuinticNat_encodeQuinticNat, he]

private theorem cosetPoint_zero (k : Nat) : cosetPoint k 0 = one := by
  rw [cosetPoint, basePower_eq, ZkHemV2.fpow_zero, QuinticGoldilocks.ofBase_one]

private theorem cosetPoint_half (k : Nat) (hk : k + 1 ≤ 32) :
    cosetPoint (k + 1) (2 ^ k) = neg one := by
  rw [cosetPoint, basePower_eq, ZkHemV2.twoAdicElem_half_pow k hk,
      QuinticGoldilocks.ofBase_neg, QuinticGoldilocks.ofBase_one]

/-- Reading each stage at positions 0 and n yields the two antipodal evaluations. -/
def examplePair (p : List K) : List K :=
  [RoundPoly.evalCoeffs p one, RoundPoly.evalCoeffs p (neg one)]

def exampleValues : List K :=
  let tape := fun p => (List.replicate 640 (examplePair p)).flatten
  let p1 := foldPolyCoeffs one examplePoly
  tape examplePoly ++ (tape p1 ++ tape (foldPolyCoeffs one p1))

private theorem examplePair_fold (p : List K) :
    foldBlock zkHemV2MultiStageEnv [one] one (examplePair p) =
      RoundPoly.evalCoeffs (foldPolyCoeffs one p) one := by
  have h0 : fiberPoint 1 one 0 = one := by rw [fiberPoint, cosetPoint_zero, LawfulCommRing.mul_one]
  have he : fiberEvaluations 1 one p = examplePair p := by
    rw [fiberEvaluations, show (List.range (2^1)) = [0,1] by decide]
    simp only [List.map_cons, List.map_nil, h0, examplePair]
    rw [show (1 : Nat) = 2^0 + 0 by rfl, fiberPoint_antipode 0 0 (by decide), h0]
  have hf := foldBlock_evalCoeffs zkHemV2MultiStageEnv (by rfl) (by rfl) [one] one p
    (by decide) (Ne.symm LawfulField.zero_ne_one)
  simpa only [List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil, he, Nat.reduceAdd,
    ZkHemV2.pow2Iter_one, LawfulCommRing.one_mul] using hf

private theorem repeatedPair_length (n : Nat) (p : List K) :
    ((List.replicate n (examplePair p)).flatten).length = n * 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul]
    change 2 + n * 2 = n * 2 + 2
    omega

private theorem repeatedPair_at (n j : Nat) (p : List K) (hj : j < n) :
    (((List.replicate n (examplePair p)).flatten).drop (j * 2)).take 2 = examplePair p := by
  induction j generalizing n with
  | zero =>
    cases n with
    | zero => omega
    | succ n => rw [List.replicate_succ, List.flatten_cons]; rfl
  | succ j ih =>
    cases n with
    | zero => omega
    | succ n =>
      rw [List.replicate_succ, List.flatten_cons, Nat.succ_mul, Nat.add_comm (j * 2) 2,
        ← List.drop_drop]
      exact ih n (by omega)

private theorem zeroSeed_field (j : Nat) : whirField 0 j = zero := by
  simp only [whirField, Nat.zero_shiftRight, Nat.zero_mod, decodeQuintic400.public_eq_1]
  have h := decodeQuinticNat_encodeQuinticNat (zero : K)
  have he : encodeQuinticNat (zero : K) = 0 := by rw [encodeQuinticNat.public_eq_1]; rfl
  rwa [he] at h

private theorem zeroSeed_pos (j n : Nat) : whirPosition 0 j n = 0 := by
  simp only [whirPosition, Nat.zero_shiftRight, Nat.zero_mod]

private theorem check_nonterminal (env : WhirEnv K) (allVs : List (StageView K)) (i : Nat)
    (st next : WhirStage) (rest : List WhirStage) (v : StageView K) (vs : List (StageView K))
    (c c' : K) (as : List K) (p tail : List K)
    (hr : stageFoldRun env i st.sumcheckDeg c v.folds = some (c', as))
    (hy : v.answer.1.answers.length = st.oodCount) (hk : st.foldK = 1)
    (hg : env.chalField v.answer.2 st.queryCount = zero) :
    whirCheckStagesAux env allVs i (st :: next :: rest) (v :: vs) c
        ((List.replicate st.queryCount (examplePair p)).flatten ++ tail) =
      whirCheckStagesAux env allVs (i + 1) (next :: rest) vs c' tail := by
  rw [whirCheckStagesAux.eq_1, hr]
  simp only [hy, decide_true, hk, hg, combineClaim_zero, List.isEmpty_cons,
    Bool.false_eq_true, ↓reduceIte, List.length_append, repeatedPair_length,
    show 2^1 = 2 by rfl, Nat.le_add_right, Bool.true_and]
  rw [← repeatedPair_length st.queryCount p, List.drop_left]

private theorem check_terminal (env : WhirEnv K) (allVs : List (StageView K)) (i : Nat)
    (st : WhirStage) (v : StageView K) (c c' : K) (as : List K) (p : List K)
    (hr : stageFoldRun env i st.sumcheckDeg c v.folds = some (c', as))
    (hy : v.answer.1.answers.length = st.oodCount) (hk : st.foldK = 1)
    (hraw : env.foldBlockRaw = none)
    (hpoint : ∀ j, env.chalPos v.answer.2 j st.domainSize = 0)
    (hfold : foldBlock env as (env.domPt i 0) (examplePair p) =
      RoundPoly.evalCoeffs v.commit.1.poly (env.domPt (i+1) 0))
    (hdeg : v.commit.1.poly.length ≤ env.finalDeg + 1)
    (hclaim : c' = match env.finalClaimViews with
      | none => env.finalClaim v.commit.1.poly as | some f => f allVs as) :
    whirCheckStagesAux env allVs i [st] [v] c (List.replicate st.queryCount (examplePair p)).flatten =
    (((List.range st.oodCount).map (env.chalField v.commit.2)).zip v.answer.1.answers).all
      (fun zy => decide (RoundPoly.evalCoeffs v.commit.1.poly zy.1 = zy.2)) := by
  have hmap : (List.range st.queryCount).map (fun j =>
      foldBlock env as (env.domPt i 0) (((List.replicate st.queryCount (examplePair p)).flatten.drop
        (j*2)).take 2)) =
      List.replicate st.queryCount (RoundPoly.evalCoeffs v.commit.1.poly (env.domPt (i+1) 0)) := by
    conv => rhs; rw [← List.length_range (n := st.queryCount), ← List.map_const (l := List.range st.queryCount)]
    apply List.map_congr_left
    intro j hj
    rw [repeatedPair_at _ _ _ (List.mem_range.mp hj), hfold]
    rfl
  rw [whirCheckStagesAux.eq_1, hr]
  simp only [hy, decide_true, hk, hraw, hpoint, List.isEmpty_nil, ↓reduceIte, repeatedPair_length,
    show 2^1 = 2 by rfl, Nat.le_refl, Bool.true_and, decide_eq_true hdeg, Bool.and_true,
    hmap]
  have ht : ((List.range st.queryCount).zip (List.replicate st.queryCount
      (RoundPoly.evalCoeffs v.commit.1.poly (env.domPt (i+1) 0)))).all
      (fun jv => decide (RoundPoly.evalCoeffs v.commit.1.poly (env.domPt (i+1) 0) = jv.2)) = true := by
    apply List.all_eq_true.mpr
    intro a ha
    exact decide_eq_true (List.eq_of_mem_replicate (List.of_mem_zip ha).2).symm
  rw [ht, Bool.and_true]
  cases hv : env.finalClaimViews <;> simp only [hv] at hclaim ⊢ <;> simp [hclaim]

private def refStage (k d a : Nat) : WhirStage := ⟨1,k,4,1,640,d,a,1,4,8,2,256⟩

private def foldOne := foldPolyCoeffs one examplePoly
private def foldTwo := foldPolyCoeffs one foldOne
private def foldThree := foldPolyCoeffs one foldTwo

private def exampleView (a b : Nat) (p : List K) (answer : K) : StageView K :=
  ⟨[(⟨[zero, embedNat a, embedNat b], []⟩, 1)], (⟨p, []⟩, 2), (⟨[], [answer]⟩, 0)⟩

private def viewsFor (answer : K) : List (StageView K) :=
  [exampleView 4 3 [] (RoundPoly.evalCoeffs foldOne (embedNat 2)),
   exampleView 4 3 [] (RoundPoly.evalCoeffs foldTwo (embedNat 2)),
   exampleView 6 1 foldThree answer]

def examplePublic (y : K) : List (WhirPub K × Nat) :=
  (exampleTranscript y).map fun (m,c) => (⟨m.poly,m.answers⟩, c)

private theorem example_split (y : K) :
    splitStages zkHemV2MultiStageSched.stages (examplePublic y) = some (viewsFor y) := by rfl

private theorem example_sumcheck (i a b : Nat) (p : List K) (y : K)
    (h : (a,b) = (4,3) ∨ (a,b) = (6,1)) :
    stageFoldRun zkHemV2MultiStageEnv i 2 (embedNat 7) (exampleView a b p y).folds =
      some (embedNat 7, [one]) := by
  rw [stageFoldRun.public_eq_1]
  change sumcheckRun zkHemV2MultiStageEnv 2 (embedNat 7)
    [(⟨[zero, embedNat a, embedNat b], []⟩, 1)] = _
  let q := [zero, embedNat a, embedNat b]
  have hd : q.length ≤ 2 + 1 := Nat.le_refl 3
  have hc : RoundPoly.evalCoeffs q zero +ᵍ RoundPoly.evalCoeffs q one = embedNat 7 := by
    rcases h with h | h <;> injection h with ea eb <;> subst a <;> subst b <;> decide +kernel
  have he : RoundPoly.evalCoeffs q one = embedNat 7 := by
    rcases h with h | h <;> injection h with ea eb <;> subst a <;> subst b <;> decide +kernel
  have ha : zkHemV2MultiStageEnv.chalField 1 0 = one := whirField_small 1 (by decide)
  rw [sumcheckRun.public_eq_2]
  change (if q.length ≤ 2+1 ∧ _ then _ else _) = _
  rw [ite_eq_left ⟨hd,hc⟩, ha, sumcheckRun.public_eq_1, he]
  rfl

private theorem example_terminalClaim (y : K) :
    terminalKernel zkHemV2MultiStageSched.stages (viewsFor y) [(one,one)] = embedNat 7 := by
  have h1 : whirField 1 0 = one := whirField_small 1 (by decide)
  simp only [zkHemV2MultiStageSched, viewsFor, exampleView, terminalKernel, List.foldl_cons,
    List.foldl_nil, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, ↓reduceIte,
    h1, zeroSeed_field, weightedPoints, List.append_nil, List.map_cons, List.map_nil]
  decide +kernel

theorem example_verdict (y : K) :
    whirVerdict zkHemV2MultiStageEnv zkHemV2MultiStageSched (embedNat 7)
      (examplePublic y) exampleValues = decide (embedNat 7 = y) := by
  rw [whirVerdict.public_eq_1, example_split]
  dsimp only
  rw [whirCheckStages.public_eq_1]
  let env := zkHemV2MultiStageEnv
  let cs := embedNat 7
  let v0 := exampleView 4 3 [] (RoundPoly.evalCoeffs foldOne (embedNat 2))
  let v1 := exampleView 4 3 [] (RoundPoly.evalCoeffs foldTwo (embedNat 2))
  let v2 := exampleView 6 1 foldThree y
  let tape := fun p => (List.replicate 640 (examplePair p)).flatten
  change whirCheckStagesAux env (viewsFor y) 0 [refStage 7 8 88, refStage 6 4 44, refStage 5 2 22]
    [v0, v1, v2] cs (tape examplePoly ++ (tape foldOne ++ tape foldTwo)) = _
  have hg : env.chalField 0 640 = zero := zeroSeed_field _
  apply Eq.trans (check_nonterminal env (viewsFor y) 0 (refStage 7 8 88) (refStage 6 4 44) _ v0 _
    cs cs [one] examplePoly (tape foldOne ++ tape foldTwo) (example_sumcheck 0 4 3 _ _ (.inl rfl)) rfl rfl hg)
  apply Eq.trans (check_nonterminal env (viewsFor y) 1 (refStage 6 4 44) (refStage 5 2 22) _ v1 _
    cs cs [one] foldOne (tape foldTwo) (example_sumcheck 1 4 3 _ _ (.inl rfl)) rfl rfl hg)
  have dom (i : Nat) : env.domPt i 0 = one := cosetPoint_zero _
  have hf : foldBlock env [one] (env.domPt 2 0) (examplePair foldTwo) =
      RoundPoly.evalCoeffs foldThree (env.domPt 3 0) := by
    rw [dom, dom]; exact examplePair_fold _
  apply Eq.trans (check_terminal env (viewsFor y) 2 (refStage 5 2 22) v2 cs cs [one] foldTwo
    (example_sumcheck 2 6 1 _ _ (.inr rfl)) rfl rfl rfl (fun j => zeroSeed_pos j _) hf
    (by change foldThree.length ≤ 2; decide +kernel) (example_terminalClaim y).symm)
  change ([env.chalField 2 0].zip [y]).all _ = _
  have h2 : env.chalField 2 0 = embedNat 2 := whirField_small _ (by decide)
  rw [h2]
  change (decide (RoundPoly.evalCoeffs foldThree (embedNat 2) = y) && true) = _
  rw [show RoundPoly.evalCoeffs foldThree (embedNat 2) = embedNat 7 by decide +kernel, Bool.and_true]

private def pairQueries (i k : Nat) : List (Nat × Nat) :=
  (List.replicate 640 [(i,0), (i,2^k)]).flatten

private theorem example_stage_queries (i k d a u v : Nat) (p : List K) (y : K) :
    stageQueries zkHemV2MultiStageEnv i (refStage k d a) (exampleView u v p y) =
      pairQueries i k := by
  rw [stageQueries.public_eq_1]
  change ((List.range 640).flatMap fun j => (List.range 2).map fun b =>
    (i, whirPosition 0 j (2^k) + b * 2^k)) = _
  simp only [zeroSeed_pos, show List.range 2 = [0,1] by decide, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.zero_add, List.flatMap_def]
  change (List.map (Function.const Nat [(i,0),(i,2^k)]) _).flatten = _
  rw [List.map_const, List.length_range]
  rfl

private theorem example_queries (y : K) : whirQueries zkHemV2MultiStageEnv zkHemV2MultiStageSched
    (examplePublic y) = pairQueries 0 7 ++ (pairQueries 1 6 ++ pairQueries 2 5) := by
  rw [whirQueries.public_eq_1, example_split]
  change allStageQueries zkHemV2MultiStageEnv 0 [refStage 7 8 88, refStage 6 4 44, refStage 5 2 22]
    (viewsFor y) = _
  simp only [viewsFor, allStageQueries.public_eq_1, allStageQueries.public_eq_2,
    example_stage_queries, List.append_nil]

private theorem exampleTable_getD (k j : Nat) (p : List K) (hj : j < 2^k) :
    (exampleTable k p).getD j zero = RoundPoly.evalCoeffs p (cosetPoint k j) := by
  rw [exampleTable, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (List.length_range ▸ hj), List.getElem_range]
  rfl

private theorem example_reads_pair (i k : Nat) (p : List K) (f : Nat × Nat → K)
    (hk : k + 1 ≤ 32) (hf : ∀ j, f (i,j) = (exampleTable (k+1) p).getD j zero) :
    (pairQueries i k).map f = (List.replicate 640 (examplePair p)).flatten := by
  have h0 := Nat.two_pow_pos k
  have h2 : 2^k < 2^(k+1) := by rw [Nat.pow_succ]; omega
  simp only [pairQueries, List.map_flatten, List.map_replicate, List.map_cons, List.map_nil,
    hf, exampleTable_getD _ 0 _ (Nat.two_pow_pos _), exampleTable_getD _ _ _ h2,
    cosetPoint_zero, cosetPoint_half _ hk, examplePair]

private theorem example_reads (y : K) :
    (whirQueries zkHemV2MultiStageEnv zkHemV2MultiStageSched (examplePublic y)).map
      (fun q => whirTable zkHemV2MultiStageSched exampleStmt ((exampleTranscript y).map Prod.fst) q.1 q.2) =
      exampleValues := by
  let f := fun q : Nat × Nat =>
    whirTable zkHemV2MultiStageSched exampleStmt ((exampleTranscript y).map Prod.fst) q.1 q.2
  change List.map f _ = _
  rw [example_queries, List.map_append, List.map_append]
  have h0 (j : Nat) : f (0,j) = (exampleTable 8 examplePoly).getD j zero := by
    rw [show f (0,j) = _ from whirTable.public_eq_1 _ _ _ j]
    rfl
  have hi0 : commitRoundIdx zkHemV2MultiStageSched.stages 0 = 1 := by
    rw [zkHemV2MultiStageSched, commitRoundIdx.public_eq_2]
  have hi1 : commitRoundIdx zkHemV2MultiStageSched.stages 1 = 4 := by
    rw [zkHemV2MultiStageSched, commitRoundIdx.public_eq_3, commitRoundIdx.public_eq_2]; rfl
  have h1 (j : Nat) : f (1,j) = (exampleTable 7 foldOne).getD j zero := by
    change whirTable _ _ _ (0+1) j = _
    rw [whirTable.public_eq_2, hi0]; rfl
  have h2 (j : Nat) : f (2,j) = (exampleTable 6 foldTwo).getD j zero := by
    change whirTable _ _ _ (1+1) j = _
    rw [whirTable.public_eq_2, hi1]; rfl
  rw [example_reads_pair 0 7 _ f (by decide) h0, example_reads_pair 1 6 _ f (by decide) h1,
    example_reads_pair 2 5 _ f (by decide) h2]
  rfl

theorem example_verify (y : K) :
    (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).verify exampleStmt
      (exampleTranscript y) = decide (embedNat 7 = y) := by
  rw [OracleIop.verify_eq]
  change (true && whirVerdict zkHemV2MultiStageEnv zkHemV2MultiStageSched exampleStmt.claim
    (examplePublic y) ((whirQueries _ _ (examplePublic y)).map _)) = _
  rw [Bool.true_and]
  apply Eq.trans (congrArg (whirVerdict zkHemV2MultiStageEnv zkHemV2MultiStageSched exampleStmt.claim
    (examplePublic y)) (example_reads y))
  exact example_verdict y

theorem zkHemV2MultiStage_honest_accepts :
    (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).verify exampleStmt
      (exampleTranscript (embedNat 7)) = true := by rw [example_verify]; decide +kernel

theorem tooth_changed_ood_rejected :
    (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).verify exampleStmt
      (exampleTranscript (embedNat 8)) = false := by rw [example_verify]; decide +kernel

theorem accepted_example_ood (y : K)
    (h : (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).verify exampleStmt
      (exampleTranscript y) = true) : y = embedNat 7 := by
  rw [example_verify, decide_eq_true_eq] at h; exact h.symm

theorem inhabited_succinctWhirAggregate_honest_accepts :
    ∃ y, (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).verify exampleStmt
      (exampleTranscript y) = true := ⟨_, zkHemV2MultiStage_honest_accepts⟩

/-! ## Equivalence with the reads and checks of the oracle verifier -/

private def pub (r : Round) : WhirPub K × Nat := (⟨r.1.poly,r.1.answers⟩, r.2)
private def mkView (f cm an : Round) : StageView K := ⟨[pub f], pub cm, pub an⟩

private def twiceMap {α β : Type} (l : List α) (a b : α → β) :=
  l.flatMap (fun j => [a j,b j])

private theorem twiceMap_length {α β : Type} (l : List α) (a b : α → β) :
    (twiceMap l a b).length = l.length*2 := by
  induction l with
  | nil => rfl
  | cons j js ih =>
    change ((twiceMap js a b).length+1+1) = (js.length+1)*2
    omega

private theorem twiceMap_at {α β : Type} (l : List α) (a b : α → β) (tail : List β)
    (j : Nat) (hj : j < l.length) :
    (((twiceMap l a b ++ tail).drop (j*2)).take 2) = [a l[j], b l[j]] := by
  induction l generalizing j with
  | nil => cases hj
  | cons z zs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      change j+1 < zs.length+1 at hj
      rw [Nat.succ_mul]
      exact ih j (by omega)

private def queryCells (st : CertStage) (i c : Nat) : List (Nat × Nat) :=
  twiceMap (shiftPositions st.log 640 (c/2^2000)) (fun j => (i,j)) (fun j => (i,j+2^st.log))

private def readStage (st : CertStage) (table : List K) (c : Nat) : List K :=
  twiceMap (shiftPositions st.log 640 (c/2^2000)) (fun j => table.getD j zero)
    (fun j => table.getD (2^st.log+j) zero)

private def CertStage.whir (st : CertStage) := refStage st.log st.coeffs st.threshold

private theorem stage_queries_exact (st : CertStage) (i : Nat) (f cm an : Round) :
    stageQueries zkHemV2MultiStageEnv i st.whir (mkView f cm an) = queryCells st i an.2 := by
  rw [stageQueries.public_eq_1]
  change (List.range 640).flatMap (fun j => ([0,1] : List Nat).map (fun b =>
    (i, whirPosition an.2 j (2^st.log) + b * 2^st.log))) = _
  simp only [queryCells, twiceMap, shiftPositions, List.flatMap_map,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, whirPosition_high]

private theorem read_stage_exact (st : CertStage) (i c : Nat) (table : List K) (g : Nat × Nat → K)
    (h : ∀ j, g (i,j) = table.getD j zero) : (queryCells st i c).map g = readStage st table c := by
  simp only [queryCells, readStage, twiceMap, List.map_flatMap, List.map_cons,
    List.map_nil, h, Nat.add_comm (2^st.log)]

private theorem readStage_length (st : CertStage) (table : List K) (c : Nat) : (readStage st table c).length = 1280 := by
  rw [readStage, twiceMap_length]; simp [shiftPositions]

private theorem foldBlock_pair (x α a b : K) :
    foldBlock zkHemV2MultiStageEnv [α] x [a,b] = quinticWhirFold2 x α a b := by
  rw [foldBlock, show zkHemV2MultiStageEnv.fiberPoint = some fiberPoint from rfl, foldBlock]
  simp only [show [a,b].length / 2 = 1 by simp, List.range_one, List.map_cons, List.map_nil, List.headD_cons]
  change quinticWhirFold2 (fiberPoint 1 x 0) α a b = _
  rw [fiberPoint, cosetPoint_zero, LawfulCommRing.mul_one]

private def getFolded (i : Nat) (an : Round) (s : Nat) (α : K) (vals : List K) :=
  (List.range 640).map (fun j =>
    foldBlock zkHemV2MultiStageEnv [α] (zkHemV2MultiStageEnv.domPt i (whirPosition an.2 j (2^s)))
      ((vals.drop (j*2)).take 2))

private theorem fold_read_stage (st : CertStage) (i : Nat) (hdom : ∀ j, zkHemV2MultiStageEnv.domPt i j = cosetPoint (st.log+1) j)
    (input : CertInput) (f an : Round) (tail : List K) :
    getFolded i an st.log (whirField f.2 0) (readStage st input.table an.2 ++ tail) =
    ((shiftPositions st.log 640 (an.2/2^2000)).map (cosetPoint st.log)).map (makeFold st input f).word := by
  simp only [getFolded, shiftPositions, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro j hj
  let qs := shiftPositions st.log 640 (an.2/2^2000)
  have hj' : j < qs.length := by simpa [qs,shiftPositions] using List.mem_range.mp hj
  have ix : qs[j] = shiftPos st.log (an.2/2^2000) j := by simp [qs,shiftPositions]
  have pair := twiceMap_at qs (fun j => input.table.getD j zero)
    (fun j => input.table.getD (2^st.log+j) zero) tail j hj'
  change ((readStage st input.table an.2 ++ tail).drop (j*2)).take 2 = _ at pair
  have hn : shiftPos st.log (an.2/2^2000) j < 2^st.log := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hs := (certStage_geom st).1
  have idx := coord_index st.log _ (by omega) hn
  rw [pair, ix, foldBlock_pair, hdom, whirPosition_high]
  simp only [makeFold, pairRoot, pairPos, pairNeg, idx]

private theorem stage_run_exact (st : CertStage) (i : Nat) (input : CertInput) (f cm an : Round) :
    stageFoldRun zkHemV2MultiStageEnv i st.whir.sumcheckDeg input.claim (mkView f cm an).folds =
      if validRound input f.1 then some ((makeFold st input f).claim,[whirField f.2 0]) else none := by
  rw [stageFoldRun.public_eq_1]
  change sumcheckRun zkHemV2MultiStageEnv 2 input.claim [pub f] = _
  rw [sumcheckRun.public_eq_2]
  simp only [pub, validRound, makeFold, sumcheckRun.public_eq_1, Option.map_some, decide_eq_true_eq]
  split <;> simp_all [show zkHemV2MultiStageEnv.chalField = whirField from rfl]

private def nextPoints (st : CertStage) (an : Round) :=
  (shiftPositions st.log 640 (an.2/2^2000)).map (cosetPoint st.log)

private theorem field640 (c : Nat) : whirField c 640 = whirField c 0 := by
  unfold whirField; rw [show 640%5=0 by decide]

private theorem nonterminal_accept (st : CertStage) (i : Nat) (hdom : ∀ j, zkHemV2MultiStageEnv.domPt i j = cosetPoint (st.log+1) j)
    (allVs : List (StageView K)) (input : CertInput) (f cm an : Round)
    (next : WhirStage) (rest : List WhirStage) (vs : List (StageView K)) (tail : List K)
    (h : whirCheckStagesAux zkHemV2MultiStageEnv allVs i (st.whir :: next :: rest)
      (mkView f cm an :: vs) input.claim (readStage st input.table an.2 ++ tail) = true) :
    validRound input f.1 = true ∧ an.1.answers.length = 1 ∧
    whirCheckStagesAux zkHemV2MultiStageEnv allVs (i+1) (next :: rest) vs
      (makeShift st (makeFold st input f) cm an).claim tail = true := by
  rw [whirCheckStagesAux.eq_1, stage_run_exact st i input f cm an] at h
  cases hv : validRound input f.1 with
  | false => rw [hv] at h; contradiction
  | true =>
    rw [hv] at h
    simp only [↓reduceIte, List.isEmpty_cons, Bool.false_eq_true,
      show zkHemV2MultiStageEnv.foldBlockRaw = none from rfl] at h
    dsimp only [mkView,pub,CertStage.whir,refStage,WhirStage.domainSize] at h
    rw [show zkHemV2MultiStageEnv.chalField = whirField from rfl, field640,
        show zkHemV2MultiStageEnv.chalPos = whirPosition from rfl] at h
    let vals := readStage st input.table an.2 ++ tail
    change (decide (an.1.answers.length = 1) && decide (1280 ≤ vals.length) &&
      whirCheckStagesAux zkHemV2MultiStageEnv allVs (i+1) (next::rest) vs
        (combineClaim (makeFold st input f).claim (whirField an.2 0)
          (an.1.answers ++ getFolded i an st.log (whirField f.2 0) vals))
        (vals.drop 1280)) = true at h
    have hd : vals.drop 1280 = tail := by change (_ ++ tail).drop 1280 = tail; rw [← readStage_length st input.table an.2, List.drop_left]
    obtain ⟨⟨hy,_⟩,h⟩ := Bool.and_eq_true_iff.mp h |>.imp Bool.and_eq_true_iff.mp id
    refine ⟨rfl, of_decide_eq_true hy, ?_⟩
    rw [hd, fold_read_stage st i hdom input f an tail] at h
    exact h

private theorem kernel_step (st : CertStage) (next : WhirStage) (rest : List WhirStage)
    (vs : List (StageView K)) (input : CertInput) (f cm an : Round) :
    terminalKernel (st.whir :: next :: rest) (mkView f cm an :: vs) input.terms =
      terminalKernel (next :: rest) vs (makeShift st (makeFold st input f) cm an).terms := by
  have pts : (List.range 640).map (fun j => cosetPoint st.log (whirPosition an.2 j (2^st.log))) =
      nextPoints st an := by simp only [nextPoints, shiftPositions, List.map_map, Function.comp_def, whirPosition_high]
  rw [terminalKernel]
  dsimp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, CertStage.whir, refStage,
    WhirStage.domainSize, mkView,pub,List.foldl_cons,List.foldl_nil]
  rw [List.range_one, List.map_cons, List.map_nil, field640, pts]
  rfl

private theorem kernel_last (input : CertInput) (f cm an : Round) :
    terminalKernel [CertStage.last.whir] [mkView f cm an] input.terms =
      kernelValue cm.1.poly (makeFold .last input f).terms := by
  rw [terminalKernel]
  change List.foldl _ zero (makeFold .last input f).terms = _
  rw [kernelValue_foldl, LawfulCommRing.zero_add]; rfl

private theorem terminal_accept (allVs : List (StageView K)) (input : CertInput) (f cm an : Round)
    (hkern : terminalKernel zkHemV2MultiStageSched.stages allVs [(one,one)] =
      kernelValue cm.1.poly (makeFold .last input f).terms)
    (h : whirCheckStagesAux zkHemV2MultiStageEnv allVs 2 [CertStage.last.whir] [mkView f cm an]
      input.claim (readStage .last input.table an.2) = true) :
    validRound input f.1 = true ∧ an.1.answers.length = 1 ∧ cm.1.poly.length ≤ 2 ∧
      terminalLive 5 640 (makeFold .last input f).word (makeFold .last input f).terms
        (makeFold .last input f).claim cm.1.poly an.2 = true := by
  rw [whirCheckStagesAux.eq_1, stage_run_exact .last 2 input f cm an] at h
  cases hv : validRound input f.1 with
  | false => rw [hv] at h; contradiction
  | true =>
    rw [hv] at h
    simp only [↓reduceIte, List.isEmpty_nil, show zkHemV2MultiStageEnv.foldBlockRaw = none from rfl] at h
    let f' := makeFold .last input f
    let vals := readStage .last input.table an.2
    let pin := fun jv : Nat × K => decide (RoundPoly.evalCoeffs cm.1.poly
      (cosetPoint 5 (whirPosition an.2 jv.1 32)) = jv.2)
    change (decide (an.1.answers.length = 1) && decide (1280 ≤ vals.length) &&
      (decide (cm.1.poly.length ≤ 2) && _ &&
        ((List.range 640).zip (getFolded 2 an 5 (whirField f.2 0) vals)).all pin &&
        decide (f'.claim = terminalKernel zkHemV2MultiStageSched.stages allVs [(one,one)]) &&
        decide (vals.length = 1280))) = true at h
    simp only [Bool.and_eq_true,decide_eq_true_eq,hkern] at h
    obtain ⟨⟨hy,_⟩,⟨⟨⟨⟨hd,_⟩,ha⟩,hcl⟩,_⟩⟩ := h
    refine ⟨rfl,hy,hd,List.all_eq_true.mpr ?_⟩
    intro j hj
    have hread := fold_read_stage .last 2 (fun _ => rfl) input f an []
    rw [List.append_nil] at hread
    change getFolded 2 an 5 (whirField f.2 0) vals = (nextPoints .last an).map f'.word at hread
    rw [hread] at ha
    let vs := (nextPoints .last an).map f'.word
    have hj' : j < ((List.range 640).zip vs).length := by
      simpa [vs,nextPoints,shiftPositions] using List.mem_range.mp hj
    have he := List.all_eq_true.mp ha _ (List.getElem_mem hj')
    have ee := of_decide_eq_true (show decide (_ = _) = true from he)
    simp only [List.getElem_zip, List.getElem_range, vs, nextPoints, shiftPositions, List.getElem_map,
      CertStage.log] at ee
    rw [show (32 : Nat) = 2^5 by decide, whirPosition_high] at ee
    exact decide_eq_true ⟨hcl, by simpa only [whirPosition_high] using ee.symm⟩

private def nine (a b c d e f g h i : Round) : List Round := [a,b,c,d,e,f,g,h,i]
private def threeViews (a b c d e f g h i : Round) := [mkView a b c,mkView d e f,mkView g h i]

private theorem parse_nine (a b c d e f g h i : Round) :
    splitStages zkHemV2MultiStageSched.stages ((nine a b c d e f g h i).map pub) =
      some (threeViews a b c d e f g h i) := by rfl

private theorem nine_reads (x : WhirStmt K) (a b c d e f g h i : Round) :
    (whirQueries zkHemV2MultiStageEnv zkHemV2MultiStageSched ((nine a b c d e f g h i).map pub)).map
      (fun p => whirTable zkHemV2MultiStageSched x ((nine a b c d e f g h i).map Prod.fst) p.1 p.2) =
      readStage .first x.table c.2 ++ (readStage .middle b.1.table f.2 ++ readStage .last e.1.table i.2) := by
  let rd := fun p : Nat × Nat => whirTable zkHemV2MultiStageSched x ((nine a b c d e f g h i).map Prod.fst) p.1 p.2
  change List.map rd _ = _
  rw [whirQueries.public_eq_1, parse_nine]
  change (allStageQueries _ 0 [CertStage.first.whir,CertStage.middle.whir,CertStage.last.whir]
    [mkView a b c,mkView d e f,mkView g h i]).map rd = _
  simp only [allStageQueries.public_eq_1, allStageQueries.public_eq_2, stage_queries_exact, List.append_nil,
    List.map_append]
  have hi0 : commitRoundIdx zkHemV2MultiStageSched.stages 0 = 1 := by
    rw [zkHemV2MultiStageSched, commitRoundIdx.public_eq_2]
  have hi1 : commitRoundIdx zkHemV2MultiStageSched.stages 1 = 4 := by
    rw [zkHemV2MultiStageSched, commitRoundIdx.public_eq_3, commitRoundIdx.public_eq_2]; rfl
  have h0 (j : Nat) : rd (0,j) = x.table.getD j zero := whirTable.public_eq_1 _ _ _ _
  have h1 (j : Nat) : rd (1,j) = b.1.table.getD j zero := by
    change whirTable _ _ _ (0+1) j = _
    rw [whirTable.public_eq_2,hi0]; rfl
  have h2 (j : Nat) : rd (2,j) = e.1.table.getD j zero := by
    change whirTable _ _ _ (1+1) j = _
    rw [whirTable.public_eq_2,hi1]; rfl
  rw [read_stage_exact _ 0 _ _ rd h0, read_stage_exact _ 1 _ _ rd h1, read_stage_exact _ 2 _ _ rd h2]

private theorem cert_nine_accept (x : WhirStmt K) (a b c d e f g h i : Round)
    (ha : (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).verify x
      (nine a b c d e f g h i) = true) : ((nine a b c d e f g h i).foldl certStep (certStart x)).live = true := by
  let vs := threeViews a b c d e f g h i
  let inp : CertInput := ⟨x.table,[(one,one)],x.claim⟩
  let mid := makeShift .first (makeFold .first inp a) b c
  let last := makeShift .middle (makeFold .middle mid d) e f
  rw [OracleIop.verify_eq] at ha
  change (true && whirVerdict zkHemV2MultiStageEnv zkHemV2MultiStageSched x.claim
    ((nine a b c d e f g h i).map pub)
    ((whirQueries zkHemV2MultiStageEnv zkHemV2MultiStageSched ((nine a b c d e f g h i).map pub)).map
      (fun q => whirTable zkHemV2MultiStageSched x ((nine a b c d e f g h i).map Prod.fst) q.1 q.2))) = true at ha
  rw [Bool.true_and, nine_reads, whirVerdict.public_eq_1, parse_nine] at ha
  change whirCheckStages zkHemV2MultiStageEnv 0 zkHemV2MultiStageSched.stages vs inp.claim _ = true at ha
  rw [whirCheckStages.public_eq_1] at ha
  change whirCheckStagesAux _ vs 0 [CertStage.first.whir,CertStage.middle.whir,CertStage.last.whir]
    [mkView a b c,mkView d e f,mkView g h i] inp.claim _ = true at ha
  obtain ⟨h0,hy0,ha⟩ := nonterminal_accept .first 0 (fun _ => rfl) vs inp a b c _ _ _ _ ha
  obtain ⟨h1,hy1,ha⟩ := nonterminal_accept .middle 1 (fun _ => rfl) vs mid d e f _ _ _ _ ha
  have hk : terminalKernel zkHemV2MultiStageSched.stages vs [(one,one)] =
      kernelValue h.1.poly (makeFold .last last g).terms := by
    change terminalKernel [CertStage.first.whir,CertStage.middle.whir,CertStage.last.whir]
      [mkView a b c,mkView d e f,mkView g h i] inp.terms = _
    rw [kernel_step .first _ _ _ inp, kernel_step .middle _ _ _ mid, kernel_last]
  obtain ⟨h2,hy2,hd,hf⟩ := terminal_accept vs last g h i hk ha
  change (List.foldl certStep (.input .first inp) [a,b,c,d,e,f,g,h,i]).live = true
  simp only [List.foldl_cons, certStep, h0,hy0,h1,hy1,h2,hy2,hd, ↓reduceIte, decide_true,
    List.foldl_nil,CertPhase.live,Bool.true_and,mid,last] at *
  exact hf


/-! ## The schedule certificate and succinct QROM bound -/

private def certState (x : WhirStmt K) (tr : List Round) := (tr.foldl certStep (certStart x)).live

private theorem cert_accept (x : WhirStmt K) (tr : List Round)
    (h : (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).verify x tr = true) :
    certState x tr = true := by
  have hv := h
  rw [OracleIop.verify_eq] at hv
  have hlen : tr.length = 9 := of_decide_eq_true (Bool.and_eq_true_iff.mp hv).1
  obtain ⟨a, tr, rfl⟩ : ∃ x xs, tr = x::xs := by cases tr with
    | nil => simp at hlen
    | cons x xs => exact ⟨x,xs,rfl⟩
  obtain ⟨b, tr, rfl⟩ : ∃ x xs, tr = x::xs := by cases tr with
    | nil => simp at hlen
    | cons x xs => exact ⟨x,xs,rfl⟩
  obtain ⟨c, tr, rfl⟩ : ∃ x xs, tr = x::xs := by cases tr with
    | nil => simp at hlen
    | cons x xs => exact ⟨x,xs,rfl⟩
  obtain ⟨d, tr, rfl⟩ : ∃ x xs, tr = x::xs := by cases tr with
    | nil => simp at hlen
    | cons x xs => exact ⟨x,xs,rfl⟩
  obtain ⟨e, tr, rfl⟩ : ∃ x xs, tr = x::xs := by cases tr with
    | nil => simp at hlen
    | cons x xs => exact ⟨x,xs,rfl⟩
  obtain ⟨f, tr, rfl⟩ : ∃ x xs, tr = x::xs := by cases tr with
    | nil => simp at hlen
    | cons x xs => exact ⟨x,xs,rfl⟩
  obtain ⟨g, tr, rfl⟩ : ∃ x xs, tr = x::xs := by cases tr with
    | nil => simp at hlen
    | cons x xs => exact ⟨x,xs,rfl⟩
  obtain ⟨hh, tr, rfl⟩ : ∃ x xs, tr = x::xs := by cases tr with
    | nil => simp at hlen
    | cons x xs => exact ⟨x,xs,rfl⟩
  obtain ⟨i, tr, rfl⟩ : ∃ x xs, tr = x::xs := by cases tr with
    | nil => simp at hlen
    | cons x xs => exact ⟨x,xs,rfl⟩
  have hn : tr.length = 0 := by simp only [List.length_cons] at hlen; omega
  obtain rfl := List.eq_nil_of_length_eq_zero hn
  exact cert_nine_accept x a b c d e f g hh i h

private theorem cert_covers (r : Fin zkHemV2MultiStageSched.numRounds) :
    RatBound.le ⟨certBudget r.val, 2^22480, Nat.two_pow_pos _⟩
      (zkHemV2MultiStageSched.roundBounds.getD r.val RatBound.one) := by
  rcases r with ⟨r,hr⟩
  change r < 9 at hr
  have casesR : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases casesR with h|h|h|h|h|h|h|h|h <;> subst r <;>
    rw [WhirVerifierSchedule.roundBounds_eq] <;>
    simp only [zkHemV2MultiStageSched,stagesRoundBounds_cons,stagesRoundBounds_nil,
      WhirStage.roundBounds_eq,WhirStage.foldBound_eq,WhirStage.shiftBound_eq,WhirStage.oodBound_eq,binom2_eq] <;>
    unfold certBudget <;> decide +kernel

/-- Constructive nine-round WHIR certificate on 256 → 128 → 64 → 32 scalar cells. -/
def zkHemV2MultiStageCert : WhirScheduleCert zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 where
  cert := {
    state := certState
    bad := fun r => certBudget r.val
    init := certStart_false
    accept := cert_accept
    flip := by
      intro x _ r pre m hlen hfalse
      have hr := certRound_run 0 (certStart x) pre (show 0%3=0 by decide)
      rw [Nat.zero_add, hlen] at hr
      change qsum (2^22480) (fun c => if certState x (pre ++ [(m,c.val)]) then 1 else 0) ≤ _
      simp only [certState,List.foldl_append,List.foldl_cons,List.foldl_nil]
      exact certPhase_flip _ r.val hr hfalse m
  }
  covers := cert_covers

/-- The closed succinct QROM reduction for the certified schedule. The remaining
    hypotheses are the Merkle root reconstruction and false-statement conditions. -/
theorem zkHemV2MultiStage_succinct_closed_qrom_soundness {D : Type} [DecidableEq D] {cardX cardAnc Q : Nat}
    (M : MerkleSetup D K)
    (dfltRoot : D)
    (codec : FsCodec (SuccinctRoundMsg D (WhirPub K)) zkHemV2MultiStageSched.numRounds cardX)
    (aux : Fin cardX → List (K × List D))
    (claim : K) (initRoots : Nat → D) (tblOf : Nat → D → Nat → K)
    (hx : ¬ whirInLang zkHemV2MultiStageEnv zkHemV2MultiStageSched
      ((whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot).liftStmt claim initRoots tblOf))
    (hRoots : ∀ (H : Fin cardX → BitVec 22480) (o : Fin cardX),
      succinctFsAccept (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480)
        (whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot) M codec aux claim initRoots H o = true →
      let str := fsTranscript codec H (codec.dec o)
      ∀ q ∈ (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).queries claim (str.map (fun sc' => (sc'.1.pub, sc'.2))),
        M.root q.1 ((whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).depth q.1)
          (tblOf q.1 ((whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)) =
          (whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot).rootsOf initRoots (str.map Prod.fst) q.1)
    (A : QuantumAdv cardX 22480 cardAnc Q) :
    RatBound.le
      ⟨uniformOracleSum 22480 cardX (fun H =>
          QVec.queryMassOn
            (succinctFsAccept (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480)
              (whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot) M codec aux claim initRoots H)
            (runQuantumAdv A H)),
        (2 ^ 22480) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 22480))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (RatBound.add (scheduleQromError zkHemV2MultiStageSched Q)
        ⟨uniformOracleSum 22480 cardX (fun H =>
            QVec.queryMassOn
              (succinctFsCollisionEvent (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480)
                (whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot) M codec aux claim initRoots tblOf H)
              (runQuantumAdv A H)),
          (2 ^ 22480) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
          Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 22480))
            (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩) :=
  whir_succinct_closed_qrom_soundness _ _ M dfltRoot zkHemV2MultiStageCert codec aux claim initRoots tblOf hx hRoots A

theorem zkHemV2MultiStage_succinct_qrom_128 {D : Type} [DecidableEq D] {cardX cardAnc Q : Nat}
    (M : MerkleSetup D K)
    (dfltRoot : D)
    (codec : FsCodec (SuccinctRoundMsg D (WhirPub K)) zkHemV2MultiStageSched.numRounds cardX)
    (aux : Fin cardX → List (K × List D))
    (claim : K) (initRoots : Nat → D) (tblOf : Nat → D → Nat → K)
    (hx : ¬ whirInLang zkHemV2MultiStageEnv zkHemV2MultiStageSched
      ((whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot).liftStmt claim initRoots tblOf))
    (hRoots : ∀ (H : Fin cardX → BitVec 22480) (o : Fin cardX),
      succinctFsAccept (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480)
        (whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot) M codec aux claim initRoots H o = true →
      let str := fsTranscript codec H (codec.dec o)
      ∀ q ∈ (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).queries claim (str.map (fun sc' => (sc'.1.pub, sc'.2))),
        M.root q.1 ((whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480).depth q.1)
          (tblOf q.1 ((whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)) =
          (whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot).rootsOf initRoots (str.map Prod.fst) q.1)
    (A : QuantumAdv cardX 22480 cardAnc Q) (prof : WhirCommitmentProfile) (hQ : Q ≤ 2^64)

    (hMerkle : RatBound.le
        ⟨uniformOracleSum 22480 cardX (fun H =>
            QVec.queryMassOn
              (succinctFsCollisionEvent (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480)
                (whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot) M codec aux claim initRoots tblOf H)
              (runQuantumAdv A H)),
          (2 ^ 22480) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
          Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 22480))
            (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩ (merkleProfileQromBound prof Q)) :
    RatBound.lt
      ⟨uniformOracleSum 22480 cardX (fun H =>
          QVec.queryMassOn
            (succinctFsAccept (whirOracleIop zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480)
              (whirSuccinctBridge zkHemV2MultiStageEnv zkHemV2MultiStageSched 22480 dfltRoot) M codec aux claim initRoots H)
            (runQuantumAdv A H)),
        (2 ^ 22480) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 22480))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (RatBound.invPow2 128) := by
  have closed := zkHemV2MultiStage_succinct_closed_qrom_soundness M dfltRoot codec aux claim initRoots tblOf hx hRoots A
  apply ratBound_lt_of_le_of_lt_packed (RatBound.le_trans closed (RatBound.add_le_add (RatBound.le_refl _) hMerkle))
  have hb := zkHemV2MultiStage_tree_qrom_lt_128_at_2pow64 prof (d := 0) (by decide) hQ
  simpa only [show 2^(0+1)-1=1 by decide, RatBound.scale, Nat.one_mul] using hb

#verify_kernel zkHemV2MultiStageCert
#verify_constructive zkHemV2MultiStage_succinct_qrom_128 cert_accept cert_covers zkHemV2MultiStage_succinct_closed_qrom_soundness
  twiceMap_length twiceMap_at stage_queries_exact read_stage_exact readStage_length foldBlock_pair
  fold_read_stage stage_run_exact field640 nonterminal_accept kernel_step kernel_last terminal_accept
  parse_nine nine_reads cert_nine_accept

#verify_inhabited accepted_example_ood inhabited_succinctWhirAggregate_honest_accepts
#tooth_pair zkHemV2MultiStage_honest_accepts vs tooth_changed_ood_rejected

#verify_constructive foldedLive_eq certRound_step certRound_run certStart_false certStage_geom certInput_flip
  certShift_budget_eq shift_live_eq certCommit_flip certPhase_flip
  terminalLive_mass multiStage_shift_budget false_word_agrees shiftTableLive_mass
  eq_of_length_trim shiftBatchLive_mass
  wordLive_iff close_word_candidate_unique scalar_agreement table_fold_flip
  whirPosition_high whirField_low shift_field_mass
  stageDomain_nodup domain_at coord_index pairRoot_spec cosetPoint_opposite
  pair_agreement_to_scalar multiStage_first_fold_flip multiStage_fold_budget
  foldClaimLive_seed_bound whirField_predicate_mass whirField_fold_bad_seeds whirPosition_all_good_seeds
  foldPolyCoeffs_length kernelValue_congr close_candidate_fold_eq close_fold_wrong_claim
  eval_split quinticWhirFold2_evalCoeffs basePower_eq cosetPoint_table
  fiberPoint_antipode fiberPoint_square mul_nonzero fiberPoint_ne_zero fiberEvaluations_getD
  example_all_three_odd_parts foldBlock_evalCoeffs foldKernelTerm_endpoints kernelValue_foldl kernel_fold_quadratic kernel_wrong_claim_challenges
  kernelValue_append kernelValue_weighted kernelValue_batch batch_wrong_claim_challenges
  packedQuinticWhir_geometry zkHemV2MultiStage_geometry
  zkHemV2MultiStage_tree_qrom_lt_128_at_2pow64 combineClaim_zero whirField_small
  root_stride power_stride cosetPoint_strided cosetPoint_folded cosetPoint_ne_zero foldBlock_stageQueries
  interleave_recovers_pair antipodal_foldRound_mass quinticFold_exceptional_challenges foldRound_exception_mass cosetPoint_zero cosetPoint_half examplePair_fold repeatedPair_length repeatedPair_at
  zeroSeed_field zeroSeed_pos check_nonterminal check_terminal example_split example_sumcheck
  example_terminalClaim example_verdict example_stage_queries example_queries exampleTable_getD
  example_reads_pair example_reads example_verify zkHemV2MultiStage_honest_accepts
  tooth_changed_ood_rejected accepted_example_ood inhabited_succinctWhirAggregate_honest_accepts

end Qsag.SuccinctWhirAgg
end

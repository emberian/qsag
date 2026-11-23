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

def whirPosition (c j n : Nat) : Nat := ((c >>> (2000 + 32 * j)) % 2 ^ 32) % n

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

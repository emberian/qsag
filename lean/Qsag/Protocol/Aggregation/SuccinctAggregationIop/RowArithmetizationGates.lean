module
/-
# Limb Decomposition, WOTS+C Chain, Merkle, Sponge, and `H_msg` Row Gates (`trace.rs`)

The 63-bit base-4 limb decomposition and the `H_msg` target-sum gates, the quadratic
multiplexer, the unary WOTS+C chain gate, the 2-block Merkle node gates with their witness
builders, the 2-rate sponge absorption gates, and the `H_msg` sponge arithmetization, each
with residuals that vanish exactly on the honest witness.
-/

public import Qsag.Protocol.Aggregation.SuccinctAggregationIop.Poseidon2PermRowGates

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv
set_option autoImplicit false
set_option exponentiation.threshold 2048
attribute [local irreducible] verifyUpperLayers
attribute [local irreducible] computeMessageMu
attribute [local irreducible] verifyAggNativeSigStateful verifyAggNativeSigStateless

/-! ### 63-Bit Base-4 Limb Decomposition & `H_msg` Target-Sum Gates (`trace.rs:104`) -/

/-- Reconstruct a `Goldilocks` field element from LSB-first base-4 digit wires. -/
def evalGoldilocksBase4 : List Goldilocks → Goldilocks
  | [] => Goldilocks.zero
  | d :: ds => Goldilocks.add d (Goldilocks.mul (Goldilocks.ofNat 4) (evalGoldilocksBase4 ds))

theorem evalBase4Digits_lt_pow4 :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < 4) → evalBase4Digits ds < 4 ^ ds.length
  | [], _ => by simp [evalBase4Digits]
  | d :: ds, hLt => by
    have hd : d < 4 := hLt d (List.mem_cons_self ..)
    have ih := evalBase4Digits_lt_pow4 ds (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    simp only [evalBase4Digits, List.length_cons, Nat.pow_succ]
    omega

theorem extractLimbBase4Digits_unique :
    ∀ (ds : List Nat) (q : Nat),
      (∀ d ∈ ds, d < 4) →
      extractLimbBase4Digits ds.length (evalBase4Digits ds + (4 ^ ds.length) * q) = ds ∧
      (evalBase4Digits ds + (4 ^ ds.length) * q) / (4 ^ ds.length) = q
  | [], q, _ => by
    simp [extractLimbBase4Digits, evalBase4Digits]
  | d :: ds, q, hLt => by
    have hd : d < 4 := hLt d (List.mem_cons_self ..)
    have ih := extractLimbBase4Digits_unique ds q (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    let m := evalBase4Digits ds + (4 ^ ds.length) * q
    have hRew : evalBase4Digits (d :: ds) + (4 ^ (d :: ds).length) * q = d + 4 * m := by
      dsimp only [evalBase4Digits, List.length_cons, m]
      have hPow : 4 ^ (ds.length + 1) = 4 * 4 ^ ds.length := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hPow, Nat.mul_assoc, Nat.mul_add, Nat.add_assoc]
    have hMod : (d + 4 * m) % 4 = d := by omega
    have hDiv4 : (d + 4 * m) / 4 = m := by omega
    refine ⟨?_, ?_⟩
    · rw [hRew]
      dsimp only [List.length_cons, extractLimbBase4Digits]
      rw [hMod, hDiv4, ih.1]
    · rw [hRew]
      dsimp only [List.length_cons]
      have hPow : 4 ^ (ds.length + 1) = 4 * 4 ^ ds.length := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hPow, ← Nat.div_div_eq_div_mul, hDiv4, ih.2]

theorem evalGoldilocksBase4_val_of_lt4 :
    ∀ (ds : List Goldilocks),
      ds.length ≤ 31 →
      (∀ d ∈ ds, d.val < 4) →
      (evalGoldilocksBase4 ds).val = evalBase4Digits (ds.map Goldilocks.val)
  | [], _, _ => rfl
  | d :: ds, hLen, hLt => by
    have hd : d.val < 4 := hLt d (List.mem_cons_self ..)
    have hDsLen : ds.length ≤ 30 := by simp only [List.length_cons] at hLen; omega
    have ih := evalGoldilocksBase4_val_of_lt4 ds (by omega)
      (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    have hEvalLt : evalBase4Digits (ds.map Goldilocks.val) < 4 ^ ds.length := by
      have hMapLt : ∀ v ∈ ds.map Goldilocks.val, v < 4 := by
        intro v hv
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
        exact hLt x (List.mem_cons_of_mem _ hx)
      simpa only [List.length_map] using evalBase4Digits_lt_pow4 (ds.map Goldilocks.val) hMapLt
    have hPowBound : 4 ^ (ds.length + 1) ≤ 4 ^ 31 :=
      Nat.pow_le_pow_right (by decide) hLen
    have hPowLtP : 4 ^ 31 < goldilocksPrime := by decide
    have hMulLt : 4 * (evalGoldilocksBase4 ds).val < goldilocksPrime := by
      rw [ih]
      have hStep : 4 * evalBase4Digits (ds.map Goldilocks.val) < 4 ^ (ds.length + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]; omega
      exact Nat.lt_trans (Nat.lt_of_lt_of_le hStep hPowBound) hPowLtP
    have h4Val : (Goldilocks.ofNat 4).val = 4 := rfl
    have hMulVal : (Goldilocks.mul (Goldilocks.ofNat 4) (evalGoldilocksBase4 ds)).val =
        4 * evalBase4Digits (ds.map Goldilocks.val) := by
      rw [Goldilocks.mul_val, h4Val, Nat.mod_eq_of_lt hMulLt, ih]
    have hAddLt : d.val + 4 * evalBase4Digits (ds.map Goldilocks.val) < goldilocksPrime := by
      have hStep : d.val + 4 * evalBase4Digits (ds.map Goldilocks.val) < 4 ^ (ds.length + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]; omega
      exact Nat.lt_trans (Nat.lt_of_lt_of_le hStep hPowBound) hPowLtP
    dsimp only [evalGoldilocksBase4, List.map_cons, evalBase4Digits]
    rw [Goldilocks.add_val, hMulVal, Nat.mod_eq_of_lt hAddLt]
    rfl

/-- Witness for `HmsgDecompLimb` / `StatelessDecompLimb` (`31` base-4 digits + `b62` bit, `trace.rs:104`). -/
structure Limb63DecompWitness where
  limbVal : Goldilocks
  digits  : List Goldilocks
  topBit  : Goldilocks
  deriving DecidableEq, Repr

@[expose] def honestLimb63DecompWitness (limbVal : Goldilocks) : Limb63DecompWitness where
  limbVal := limbVal
  digits  := (extractLimbBase4Digits 31 limbVal.val).map Goldilocks.ofNat
  topBit  := Goldilocks.ofNat (limbVal.val / (4 ^ 31))

def limb63DecompResiduals (expectedLimb : Goldilocks) (w : Limb63DecompWitness) : List Goldilocks :=
  if w.digits.length == 31 then
    let recon := Goldilocks.add (evalGoldilocksBase4 w.digits)
      (Goldilocks.mul (Goldilocks.ofNat (4 ^ 31)) w.topBit)
    [Goldilocks.sub w.limbVal expectedLimb,
     boolBitResidual w.topBit,
     Goldilocks.sub recon w.limbVal] ++
      w.digits.map quarticBase4
  else
    [Goldilocks.one]

private theorem map_quarticBase4_allZero_iff (ds : List Goldilocks) :
    allZeroGoldilocks (ds.map quarticBase4) = true ↔ (∀ d ∈ ds, d.val < 4) := by
  induction ds with
  | nil => simp [allZeroGoldilocks]
  | cons d ds ih =>
    have hCons : allZeroGoldilocks (quarticBase4 d :: ds.map quarticBase4) =
        ((quarticBase4 d == Goldilocks.zero) && allZeroGoldilocks (ds.map quarticBase4)) := rfl
    simp only [List.map_cons, hCons, Bool.and_eq_true, beq_iff_eq, quarticBase4_eq_zero_iff,
      ih, List.mem_cons, forall_eq_or_imp]

theorem limb63DecompResiduals_allZero_iff (expectedLimb : Goldilocks) (w : Limb63DecompWitness) :
    allZeroGoldilocks (limb63DecompResiduals expectedLimb w) = true ↔
      (expectedLimb.val < 2 ^ 63 ∧ w = honestLimb63DecompWitness expectedLimb) := by
  unfold limb63DecompResiduals
  cases hLenBeq : (w.digits.length == 31)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hF : allZeroGoldilocks [Goldilocks.one] = false := by decide
    rw [hF]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨_, rfl⟩
    simp [honestLimb63DecompWitness, extractLimbBase4Digits_length] at hLenBeq
  · have hLen : w.digits.length = 31 := eq_of_beq hLenBeq
    simp only [↓reduceIte]
    have hHeadSplit : ∀ (r0 r1 r2 : Goldilocks) (rest : List Goldilocks),
        allZeroGoldilocks ([r0, r1, r2] ++ rest) =
          ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero) &&
           (r2 == Goldilocks.zero) && allZeroGoldilocks rest) := by
      intro r0 r1 r2 rest
      simp [allZeroGoldilocks, Bool.and_assoc]
    rw [hHeadSplit]
    simp only [Bool.and_eq_true, beq_iff_eq, gold_sub_eq_zero_iff,
      boolBitResidual_eq_zero_iff, map_quarticBase4_allZero_iff]
    constructor
    · rintro ⟨⟨⟨hLimbEq, hBit⟩, hRecon⟩, hDigitsLt4⟩
      subst hLimbEq
      have hTopLt2 : w.topBit.val < 2 := by
        rcases hBit with h0 | h1
        · rw [h0]; decide
        · rw [h1]; decide
      have hEvalVal := evalGoldilocksBase4_val_of_lt4 w.digits (by omega) hDigitsLt4
      have hEvalBound : evalBase4Digits (w.digits.map Goldilocks.val) < 4 ^ 31 := by
        have hMapLt : ∀ v ∈ w.digits.map Goldilocks.val, v < 4 := by
          intro v hv
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact hDigitsLt4 x hx
        have hB := evalBase4Digits_lt_pow4 (w.digits.map Goldilocks.val) hMapLt
        simpa only [List.length_map, hLen] using hB
      have hPowEq : (4 : Nat) ^ 31 = 2 ^ 62 := rfl
      have hPowVal : (Goldilocks.ofNat (4 ^ 31)).val = 4 ^ 31 := by decide
      have hTopProdLtP : (4 ^ 31) * w.topBit.val < goldilocksPrime := by
        have h263 : (2 : Nat) ^ 63 < goldilocksPrime := by decide
        have hLe : (4 ^ 31) * w.topBit.val ≤ 2 ^ 62 := by rw [hPowEq]; omega
        omega
      have hTopMulVal : (Goldilocks.mul (Goldilocks.ofNat (4 ^ 31)) w.topBit).val =
          (4 ^ 31) * w.topBit.val := by
        rw [Goldilocks.mul_val, hPowVal, Nat.mod_eq_of_lt hTopProdLtP]
      have hSumLt263 : evalBase4Digits (w.digits.map Goldilocks.val) + (4 ^ 31) * w.topBit.val < 2 ^ 63 := by
        have h263 : (2 : Nat) ^ 63 = 2 ^ 62 + 2 ^ 62 := rfl
        rw [hPowEq] at hEvalBound ⊢
        omega
      have hSumLtP : evalBase4Digits (w.digits.map Goldilocks.val) + (4 ^ 31) * w.topBit.val < goldilocksPrime :=
        Nat.lt_trans hSumLt263 (by decide)
      have hReconVal : w.limbVal.val =
          evalBase4Digits (w.digits.map Goldilocks.val) + (4 ^ 31) * w.topBit.val := by
        have hV := congrArg Goldilocks.val hRecon.symm
        rw [Goldilocks.add_val, hEvalVal, hTopMulVal, Nat.mod_eq_of_lt hSumLtP] at hV
        exact hV
      have hLimbLt263 : w.limbVal.val < 2 ^ 63 := hReconVal ▸ hSumLt263
      have hMapLt4 : ∀ v ∈ w.digits.map Goldilocks.val, v < 4 := by
        intro v hv; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv; exact hDigitsLt4 x hx
      have hMapLen : (w.digits.map Goldilocks.val).length = 31 := by simp [hLen]
      obtain ⟨hUniqDs, hUniqQ⟩ := extractLimbBase4Digits_unique (w.digits.map Goldilocks.val) w.topBit.val hMapLt4
      rw [hMapLen, ← hReconVal] at hUniqDs hUniqQ
      have hDigitsEq : w.digits = (extractLimbBase4Digits 31 w.limbVal.val).map Goldilocks.ofNat := by
        rw [hUniqDs, List.map_map]
        have hId : (Goldilocks.ofNat ∘ Goldilocks.val) = id := by
          funext x
          exact Goldilocks.ext (Nat.mod_eq_of_lt x.isLt)
        rw [hId, List.map_id]
      have hTopEq : w.topBit = Goldilocks.ofNat (w.limbVal.val / (4 ^ 31)) := by
        rw [hUniqQ]
        exact (Goldilocks.ext (Nat.mod_eq_of_lt w.topBit.isLt)).symm
      refine ⟨hLimbLt263, ?_⟩
      rcases w with ⟨lv, ds, tb⟩
      simp only [honestLimb63DecompWitness, Limb63DecompWitness.mk.injEq] at hDigitsEq hTopEq ⊢
      exact ⟨trivial, hDigitsEq, hTopEq⟩
    · rintro ⟨hLt263, rfl⟩
      have hMapVal :
          ((extractLimbBase4Digits 31 expectedLimb.val).map Goldilocks.ofNat).map Goldilocks.val =
          extractLimbBase4Digits 31 expectedLimb.val := by
        rw [List.map_map]
        have hIdOnLt4 : ∀ x ∈ extractLimbBase4Digits 31 expectedLimb.val,
            (Goldilocks.ofNat x).val = x := by
          intro x hx
          have hx4 := extractLimbBase4Digits_all_lt_four 31 expectedLimb.val x hx
          exact Nat.mod_eq_of_lt (Nat.lt_trans hx4 (by decide))
        exact list_map_eq_self_of_forall _ hIdOnLt4
      have hDsLt4 : ∀ d ∈ (honestLimb63DecompWitness expectedLimb).digits, d.val < 4 := by
        intro d hd
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
        have hx4 := extractLimbBase4Digits_all_lt_four 31 expectedLimb.val x hx
        have hVal : (Goldilocks.ofNat x).val = x := Nat.mod_eq_of_lt (Nat.lt_trans hx4 (by decide))
        omega
      have hDivLt2 : expectedLimb.val / (4 ^ 31) < 2 := by
        have hPowEq : (4 : Nat) ^ 31 = 2 ^ 62 := rfl
        have h263 : (2 : Nat) ^ 63 = 2 * 2 ^ 62 := rfl
        rw [hPowEq]; rw [h263] at hLt263; omega
      have hBitOr : (honestLimb63DecompWitness expectedLimb).topBit = Goldilocks.zero ∨
                    (honestLimb63DecompWitness expectedLimb).topBit = Goldilocks.one := by
        dsimp only [honestLimb63DecompWitness]
        cases hQ : expectedLimb.val / (4 ^ 31) with
        | zero => exact .inl (Goldilocks.ext rfl)
        | succ m =>
          have hm0 : m = 0 := by omega
          subst hm0
          exact .inr (Goldilocks.ext rfl)
      have hReconEq :
          Goldilocks.add (evalGoldilocksBase4 (honestLimb63DecompWitness expectedLimb).digits)
            (Goldilocks.mul (Goldilocks.ofNat (4 ^ 31)) (honestLimb63DecompWitness expectedLimb).topBit) =
          expectedLimb := by
        apply Goldilocks.ext
        have hEV := evalGoldilocksBase4_val_of_lt4 (honestLimb63DecompWitness expectedLimb).digits
          (by simp [honestLimb63DecompWitness, extractLimbBase4Digits_length]) hDsLt4
        dsimp only [honestLimb63DecompWitness] at hEV ⊢
        rw [hMapVal] at hEV
        have hTopVal : (Goldilocks.ofNat (expectedLimb.val / (4 ^ 31))).val = expectedLimb.val / (4 ^ 31) :=
          Nat.mod_eq_of_lt (Nat.lt_trans hDivLt2 (by decide))
        have hPowVal : (Goldilocks.ofNat (4 ^ 31)).val = 4 ^ 31 := by decide
        have hDecomp := evalBase4Digits_extractLimbBase4Digits 31 expectedLimb.val
        have hMulLtP : (4 ^ 31) * (expectedLimb.val / (4 ^ 31)) < goldilocksPrime := by
          have hLtP : expectedLimb.val < goldilocksPrime := expectedLimb.isLt
          omega
        have hMulVal : (Goldilocks.mul (Goldilocks.ofNat (4 ^ 31))
            (Goldilocks.ofNat (expectedLimb.val / (4 ^ 31)))).val =
            (4 ^ 31) * (expectedLimb.val / (4 ^ 31)) := by
          rw [Goldilocks.mul_val, hPowVal, hTopVal, Nat.mod_eq_of_lt hMulLtP]
        rw [Goldilocks.add_val, hEV, hMulVal, hDecomp, Nat.mod_eq_of_lt expectedLimb.isLt]
      exact ⟨⟨⟨rfl, hBitOr⟩, hReconEq⟩, hDsLt4⟩

/-- Field sum of a list of `Goldilocks` wires. -/
def sumGoldilocks : List Goldilocks → Goldilocks
  | [] => Goldilocks.zero
  | d :: ds => Goldilocks.add d (sumGoldilocks ds)

theorem listNatSum_le_three_mul :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < 4) → listNatSum ds ≤ 3 * ds.length
  | [], _ => by simp [listNatSum]
  | d :: ds, hLt => by
    have hd : d < 4 := hLt d (List.mem_cons_self ..)
    have ih := listNatSum_le_three_mul ds (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    dsimp only [listNatSum, List.length_cons]
    omega

theorem sumGoldilocks_val_of_lt4 :
    ∀ (ds : List Goldilocks),
      ds.length ≤ 128 →
      (∀ d ∈ ds, d.val < 4) →
      (sumGoldilocks ds).val = listNatSum (ds.map Goldilocks.val)
  | [], _, _ => rfl
  | d :: ds, hLen, hLt => by
    have hd : d.val < 4 := hLt d (List.mem_cons_self ..)
    have hDsLen : ds.length ≤ 127 := by dsimp only [List.length_cons] at hLen; omega
    have ih := sumGoldilocks_val_of_lt4 ds (by omega)
      (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    have hMapLt : ∀ v ∈ ds.map Goldilocks.val, v < 4 := by
      intro v hv; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact hLt x (List.mem_cons_of_mem _ hx)
    have hTailBound : listNatSum (ds.map Goldilocks.val) ≤ 3 * ds.length := by
      simpa only [List.length_map] using listNatSum_le_three_mul (ds.map Goldilocks.val) hMapLt
    have hSumLtP : d.val + listNatSum (ds.map Goldilocks.val) < goldilocksPrime := by
      have h384 : (384 : Nat) < goldilocksPrime := by decide
      omega
    dsimp only [sumGoldilocks, List.map_cons, listNatSum]
    rw [Goldilocks.add_val, ih, Nat.mod_eq_of_lt hSumLtP]
    rfl

/-- 5-limb `Digest5` base-4 decomposition + target-sum check (`5 * HmsgDecompLimb`, `trace.rs:152`). -/
structure Hmsg5DecompWitness where
  l0 : Limb63DecompWitness
  l1 : Limb63DecompWitness
  l2 : Limb63DecompWitness
  l3 : Limb63DecompWitness
  l4 : Limb63DecompWitness
  deriving DecidableEq, Repr

@[expose] def honestHmsg5DecompWitness (d : Digest5) : Hmsg5DecompWitness where
  l0 := honestLimb63DecompWitness d.limb0
  l1 := honestLimb63DecompWitness d.limb1
  l2 := honestLimb63DecompWitness d.limb2
  l3 := honestLimb63DecompWitness d.limb3
  l4 := honestLimb63DecompWitness d.limb4

@[expose] def hmsg5DigitWires (geom : AggSigGeometry) (w : Hmsg5DecompWitness) : List Goldilocks :=
  (w.l0.digits ++ w.l1.digits ++ w.l2.digits ++ w.l3.digits ++ w.l4.digits.take 4).take geom.wotsChains

def hmsg5DecompResiduals (geom : AggSigGeometry) (expected : Digest5) (w : Hmsg5DecompWitness) :
    List Goldilocks :=
  limb63DecompResiduals expected.limb0 w.l0 ++
  limb63DecompResiduals expected.limb1 w.l1 ++
  limb63DecompResiduals expected.limb2 w.l2 ++
  limb63DecompResiduals expected.limb3 w.l3 ++
  limb63DecompResiduals expected.limb4 w.l4 ++
  [Goldilocks.sub (sumGoldilocks (hmsg5DigitWires geom w)) (Goldilocks.ofNat geom.targetSum)]

theorem map_val_ofNat_extract (k v : Nat) :
    ((extractLimbBase4Digits k v).map Goldilocks.ofNat).map Goldilocks.val =
    extractLimbBase4Digits k v := by
  rw [List.map_map]
  refine list_map_eq_self_of_forall _ fun x hx => ?_
  have hx4 := extractLimbBase4Digits_all_lt_four k v x hx
  exact Nat.mod_eq_of_lt (Nat.lt_trans hx4 (by decide))

theorem take4_extractLimbBase4Digits_31 (v : Nat) :
    (extractLimbBase4Digits 31 v).take 4 = extractLimbBase4Digits 4 v := rfl

theorem hmsg5DecompResiduals_allZero_iff
    (geom : AggSigGeometry) (expected : Digest5) (w : Hmsg5DecompWitness)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains) :
    allZeroGoldilocks (hmsg5DecompResiduals geom expected w) = true ↔
      (w = honestHmsg5DecompWitness expected ∧
       ∃ ds, extractWotsDigitsChecked geom expected = some ds ∧
             listNatSum ds = geom.targetSum ∧
             (hmsg5DigitWires geom w).map Goldilocks.val = ds) := by
  unfold hmsg5DecompResiduals
  have hSingleZero : ∀ x : Goldilocks, allZeroGoldilocks [x] = (x == Goldilocks.zero) := by
    intro x; simp [allZeroGoldilocks]
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, limb63DecompResiduals_allZero_iff,
    hSingleZero, sub_eq_zero_iff_goldilocks]
  have hHonDigitsMap :
      (hmsg5DigitWires geom (honestHmsg5DecompWitness expected)).map Goldilocks.val =
        (extractLimbBase4Digits 31 expected.limb0.val ++
         extractLimbBase4Digits 31 expected.limb1.val ++
         extractLimbBase4Digits 31 expected.limb2.val ++
         extractLimbBase4Digits 31 expected.limb3.val ++
         extractLimbBase4Digits 4 expected.limb4.val).take geom.wotsChains := by
    unfold hmsg5DigitWires honestHmsg5DecompWitness honestLimb63DecompWitness
    dsimp only
    simp only [List.map_take, List.map_append, map_val_ofNat_extract,
      take4_extractLimbBase4Digits_31]
  have hHonWiresLt4 :
      ∀ d ∈ hmsg5DigitWires geom (honestHmsg5DecompWitness expected), d.val < 4 := by
    intro d hd
    have hValMem : d.val ∈ (hmsg5DigitWires geom (honestHmsg5DecompWitness expected)).map Goldilocks.val :=
      List.mem_map_of_mem hd
    rw [hHonDigitsMap] at hValMem
    have hMem := List.mem_of_mem_take hValMem
    simp only [List.mem_append] at hMem
    rcases hMem with (((m0 | m1) | m2) | m3) | m4
    · exact extractLimbBase4Digits_all_lt_four 31 _ _ m0
    · exact extractLimbBase4Digits_all_lt_four 31 _ _ m1
    · exact extractLimbBase4Digits_all_lt_four 31 _ _ m2
    · exact extractLimbBase4Digits_all_lt_four 31 _ _ m3
    · exact extractLimbBase4Digits_all_lt_four 4 _ _ m4
  have hHonWiresLen :
      (hmsg5DigitWires geom (honestHmsg5DecompWitness expected)).length ≤ 128 := by
    unfold hmsg5DigitWires
    exact Nat.le_trans (List.length_take_le _ _) hChainsLe
  have hTargetVal : (Goldilocks.ofNat geom.targetSum).val = geom.targetSum := by
    have hLtP : geom.targetSum < goldilocksPrime := by
      have h384 : (384 : Nat) < goldilocksPrime := by decide
      omega
    exact Nat.mod_eq_of_lt hLtP
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨c0, e0⟩, ⟨c1, e1⟩⟩, ⟨c2, e2⟩⟩, ⟨c3, e3⟩⟩, ⟨c4, e4⟩⟩, hSumEq⟩
    have hWEq : w = honestHmsg5DecompWitness expected := by
      rcases w with ⟨l0, l1, l2, l3, l4⟩
      dsimp only at e0 e1 e2 e3 e4
      subst e0 e1 e2 e3 e4
      rfl
    subst hWEq
    have hChk63 : checkDigest5Limbs63 expected = true := by
      simp only [checkDigest5Limbs63.public_eqs]
      simp [c0, c1, c2, c3, c4]
    let ds := (hmsg5DigitWires geom (honestHmsg5DecompWitness expected)).map Goldilocks.val
    have hExt : extractWotsDigitsChecked geom expected = some ds := by
      simp only [extractWotsDigitsChecked.public_eqs]
      rw [hChk63]
      simp only [↓reduceIte, Option.some.injEq]
      exact hHonDigitsMap.symm
    have hSumVal := congrArg Goldilocks.val hSumEq
    rw [sumGoldilocks_val_of_lt4 _ hHonWiresLen hHonWiresLt4, hTargetVal] at hSumVal
    exact ⟨rfl, ds, hExt, hSumVal, rfl⟩
  · rintro ⟨rfl, ds, hExt, hSumDs, hMapDs⟩
    simp only [extractWotsDigitsChecked.public_eqs] at hExt
    cases hChk : checkDigest5Limbs63 expected
    · simp [hChk] at hExt
    · have hUnpack63 :
          expected.limb0.val < 2 ^ 63 ∧ expected.limb1.val < 2 ^ 63 ∧
          expected.limb2.val < 2 ^ 63 ∧ expected.limb3.val < 2 ^ 63 ∧
          expected.limb4.val < 2 ^ 63 := by
        simp only [checkDigest5Limbs63.public_eqs] at hChk
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hChk
        exact ⟨hChk.1.1.1.1, hChk.1.1.1.2, hChk.1.1.2, hChk.1.2, hChk.2⟩
      obtain ⟨c0, c1, c2, c3, c4⟩ := hUnpack63
      have hSumField :
          sumGoldilocks (hmsg5DigitWires geom (honestHmsg5DecompWitness expected)) =
          Goldilocks.ofNat geom.targetSum := by
        apply Goldilocks.ext
        rw [sumGoldilocks_val_of_lt4 _ hHonWiresLen hHonWiresLt4, hMapDs, hSumDs, hTargetVal]
      exact ⟨⟨⟨⟨⟨⟨c0, rfl⟩, ⟨c1, rfl⟩⟩, ⟨c2, rfl⟩⟩, ⟨c3, rfl⟩⟩, ⟨c4, rfl⟩⟩, hSumField⟩

/-! ### Quadratic Multiplexer, Unary WOTS+C Chain, and 2-Block Merkle Gates (`trace.rs:112-139`) -/

/-- Degree-2 selector residual `bit * (out - aTrue) + (1 - bit) * (out - aFalse)`. -/
def muxGoldilocksResidual (bit aTrue aFalse out : Goldilocks) : Goldilocks :=
  Goldilocks.add
    (Goldilocks.mul bit (Goldilocks.sub out aTrue))
    (Goldilocks.mul (Goldilocks.sub Goldilocks.one bit) (Goldilocks.sub out aFalse))

theorem muxGoldilocksResidual_eq_zero_iff {bit : Goldilocks}
    (hBit : bit = Goldilocks.zero ∨ bit = Goldilocks.one)
    (aTrue aFalse out : Goldilocks) :
    (muxGoldilocksResidual bit aTrue aFalse out == Goldilocks.zero) = true ↔
      out = (if bit == Goldilocks.one then aTrue else aFalse) := by
  rcases hBit with rfl | rfl
  · have hZ1 : (Goldilocks.zero == Goldilocks.one) = false := by decide
    rw [hZ1]; simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
    unfold muxGoldilocksResidual
    change CommRingOps.add
      (CommRingOps.mul CommRingOps.zero (CommRingOps.sub out aTrue))
      (CommRingOps.mul (CommRingOps.sub CommRingOps.one CommRingOps.zero) (CommRingOps.sub out aFalse)) =
      CommRingOps.zero ↔ out = aFalse
    rw [LawfulCommRing.zero_mul, LawfulCommRing.zero_add,
        LawfulCommRing.sub_zero, LawfulCommRing.one_mul]
    exact LawfulCommRing.sub_eq_zero_iff
  · simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq]
    unfold muxGoldilocksResidual
    change CommRingOps.add
      (CommRingOps.mul CommRingOps.one (CommRingOps.sub out aTrue))
      (CommRingOps.mul (CommRingOps.sub CommRingOps.one CommRingOps.one) (CommRingOps.sub out aFalse)) =
      CommRingOps.zero ↔ out = aTrue
    rw [LawfulCommRing.one_mul, LawfulCommRing.sub_self,
        LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    exact LawfulCommRing.sub_eq_zero_iff

def muxDigest4Residuals (bit : Goldilocks) (aTrue aFalse out : Digest4) : List Goldilocks :=
  [muxGoldilocksResidual bit aTrue.x0 aFalse.x0 out.x0,
   muxGoldilocksResidual bit aTrue.x1 aFalse.x1 out.x1,
   muxGoldilocksResidual bit aTrue.x2 aFalse.x2 out.x2,
   muxGoldilocksResidual bit aTrue.x3 aFalse.x3 out.x3]

theorem muxDigest4Residuals_allZero_iff {bit : Goldilocks}
    (hBit : bit = Goldilocks.zero ∨ bit = Goldilocks.one)
    (aTrue aFalse out : Digest4) :
    allZeroGoldilocks (muxDigest4Residuals bit aTrue aFalse out) = true ↔
      out = (if bit == Goldilocks.one then aTrue else aFalse) := by
  rcases aTrue with ⟨t0, t1, t2, t3⟩
  rcases aFalse with ⟨f0, f1, f2, f3⟩
  rcases out with ⟨o0, o1, o2, o3⟩
  unfold muxDigest4Residuals allZeroGoldilocks
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    muxGoldilocksResidual_eq_zero_iff hBit]
  cases (bit == Goldilocks.one) <;> simp [Lane4.mk.injEq]

def wotsStepTweak4 (layer treeIdx kpIdx chainIdx stepIdx : Nat) : Digest4 :=
  ⟨domainWotsStep,
   packWotsAddrLimb layer kpIdx chainIdx stepIdx,
   Goldilocks.ofNat (treeIdx % (2 ^ 32)),
   Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩

/-- Unary 3-step WOTS+C chain witness (`WotsChainStep0/1/2` in `trace.rs:112-125`). -/
structure UnaryWotsChainWitness where
  act0   : Goldilocks
  act1   : Goldilocks
  act2   : Goldilocks
  sigVal : Digest4
  s1     : Digest4
  s2     : Digest4
  endVal : Digest4
  perm0  : Poseidon2PermWitness
  perm1  : Poseidon2PermWitness
  perm2  : Poseidon2PermWitness
  deriving DecidableEq, Repr

@[expose] def honestUnaryWotsChainWitness (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx digit : Nat)
    (sigVal : Digest4) : UnaryWotsChainWitness :=
  let a0 := if digit == 0 then Goldilocks.one else Goldilocks.zero
  let a1 := if digit ≤ 1 then Goldilocks.one else Goldilocks.zero
  let a2 := if digit ≤ 2 then Goldilocks.one else Goldilocks.zero
  let p0 := honestPoseidon2PermWitness ⟨sigVal, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 0⟩
  let s1 := if a0 == Goldilocks.one then lane4Add p0.output.b0
      (poseidon2WeightedFeedForward ⟨sigVal, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 0⟩) else sigVal
  let p1 := honestPoseidon2PermWitness ⟨s1, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 1⟩
  let s2 := if a1 == Goldilocks.one then lane4Add p1.output.b0
      (poseidon2WeightedFeedForward ⟨s1, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 1⟩) else s1
  let p2 := honestPoseidon2PermWitness ⟨s2, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 2⟩
  let s3 := if a2 == Goldilocks.one then lane4Add p2.output.b0
      (poseidon2WeightedFeedForward ⟨s2, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 2⟩) else s2
  { act0 := a0, act1 := a1, act2 := a2, sigVal := sigVal,
    s1 := s1, s2 := s2, endVal := s3, perm0 := p0, perm1 := p1, perm2 := p2 }

def unaryWotsChainResiduals (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx : Nat)
    (expectedDigit : Goldilocks) (w : UnaryWotsChainWitness) : List Goldilocks :=
  let mono01 := Goldilocks.mul w.act0 (Goldilocks.sub Goldilocks.one w.act1)
  let mono12 := Goldilocks.mul w.act1 (Goldilocks.sub Goldilocks.one w.act2)
  let sumEq  := Goldilocks.sub
    (Goldilocks.add expectedDigit (Goldilocks.add w.act0 (Goldilocks.add w.act1 w.act2)))
    (Goldilocks.ofNat 3)
  [boolBitResidual w.act0, boolBitResidual w.act1, boolBitResidual w.act2, mono01, mono12, sumEq] ++
  (state12Sub w.perm0.input ⟨w.sigVal, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 0⟩).toList ++
  poseidon2PermResiduals w.perm0 ++
  muxDigest4Residuals w.act0 (lane4Add w.perm0.output.b0
      (poseidon2WeightedFeedForward ⟨w.sigVal, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 0⟩)) w.sigVal w.s1 ++
  (state12Sub w.perm1.input ⟨w.s1, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 1⟩).toList ++
  poseidon2PermResiduals w.perm1 ++
  muxDigest4Residuals w.act1 (lane4Add w.perm1.output.b0
      (poseidon2WeightedFeedForward ⟨w.s1, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 1⟩)) w.s1 w.s2 ++
  (state12Sub w.perm2.input ⟨w.s2, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 2⟩).toList ++
  poseidon2PermResiduals w.perm2 ++
  muxDigest4Residuals w.act2 (lane4Add w.perm2.output.b0
      (poseidon2WeightedFeedForward ⟨w.s2, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 2⟩)) w.s2 w.endVal

private theorem monotone_bits_sum_three_unique {d a0 a1 a2 : Goldilocks}
    (hd : d.val < 4)
    (hb0 : a0 = Goldilocks.zero ∨ a0 = Goldilocks.one)
    (hb1 : a1 = Goldilocks.zero ∨ a1 = Goldilocks.one)
    (hb2 : a2 = Goldilocks.zero ∨ a2 = Goldilocks.one)
    (hm01 : Goldilocks.mul a0 (Goldilocks.sub Goldilocks.one a1) = Goldilocks.zero)
    (hm12 : Goldilocks.mul a1 (Goldilocks.sub Goldilocks.one a2) = Goldilocks.zero)
    (hSum : Goldilocks.add d (Goldilocks.add a0 (Goldilocks.add a1 a2)) = Goldilocks.ofNat 3) :
    a0 = (if d.val == 0 then Goldilocks.one else Goldilocks.zero) ∧
    a1 = (if d.val ≤ 1 then Goldilocks.one else Goldilocks.zero) ∧
    a2 = (if d.val ≤ 2 then Goldilocks.one else Goldilocks.zero) := by
  have hdCases : d = Goldilocks.zero ∨ d = Goldilocks.one ∨
                 d = Goldilocks.ofNat 2 ∨ d = Goldilocks.ofNat 3 := by
    rcases d with ⟨v, hv⟩
    dsimp only at hd
    have hvC : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
    rcases hvC with rfl | rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl (Goldilocks.ext rfl)))
    · exact .inr (.inr (.inr (Goldilocks.ext rfl)))
  rcases hdCases with rfl | rfl | rfl | rfl <;>
    rcases hb0 with rfl | rfl <;>
    rcases hb1 with rfl | rfl <;>
    rcases hb2 with rfl | rfl <;>
    revert hm01 hm12 hSum <;> decide +kernel

private theorem wotsStepHash_eq_tweak4 (pkSeed cur : Digest4) (layer treeIdx kpIdx chainIdx stp : Nat) :
    wotsStepHash pkSeed cur layer treeIdx kpIdx chainIdx stp =
      lane4Add (poseidon2Perm12 ⟨cur, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx stp⟩).b0
        (poseidon2WeightedFeedForward ⟨cur, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx stp⟩) := by
  simp only [wotsStepHash.public_eqs, poseidon2Compress12FF.public_eqs]
  unfold wotsStepTweak4
  rw [poseidon2CompressWeighted_eq]

theorem wotsChainWalk_zero_steps (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx s : Nat)
    (cur : Digest4) :
    wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx s 0 cur = cur := by
  unfold wotsChainWalk
  rw [natIterAt]

theorem wotsChainWalk_succ_steps (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx s n : Nat)
    (cur : Digest4) :
    wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx s (n + 1) cur =
      wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx (s + 1) n
        (wotsStepHash pkSeed cur layer treeIdx kpIdx chainIdx s) := by
  unfold wotsChainWalk
  rw [natIterAt]

theorem honestUnaryWotsChainWitness_endVal
    (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx d : Nat) (sigVal : Digest4)
    (hd : d < 4) :
    (honestUnaryWotsChainWitness pkSeed layer treeIdx kpIdx chainIdx d sigVal).endVal =
      wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx d (3 - d) sigVal := by
  have hPermOut : ∀ st : Poseidon2State12, (honestPoseidon2PermWitness st).output = poseidon2Perm12 st :=
    fun st => by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
  have hCases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl
  · unfold honestUnaryWotsChainWitness
    simp only [beq_self_eq_true, Nat.zero_le, ↓reduceIte]
    rw [hPermOut, hPermOut, hPermOut]
    simp only [Nat.reduceSub, wotsChainWalk_succ_steps, wotsChainWalk_zero_steps,
      wotsStepHash_eq_tweak4, Nat.reduceAdd]
  · unfold honestUnaryWotsChainWitness
    have hZ : ((1 : Nat) == 0) = false := by decide
    have hZ1 : (Goldilocks.zero == Goldilocks.one) = false := by decide
    simp only [hZ, Bool.false_eq_true, ↓reduceIte, hZ1, Nat.le_refl,
      show (1 : Nat) ≤ 2 by decide, beq_self_eq_true]
    rw [hPermOut, hPermOut]
    simp only [Nat.reduceSub, wotsChainWalk_succ_steps, wotsChainWalk_zero_steps,
      wotsStepHash_eq_tweak4, Nat.reduceAdd]
  · unfold honestUnaryWotsChainWitness
    have hZ0 : ((2 : Nat) == 0) = false := by decide
    have hZ1 : ¬ ((2 : Nat) ≤ 1) := by decide
    have hG01 : (Goldilocks.zero == Goldilocks.one) = false := by decide
    simp only [hZ0, hZ1, Bool.false_eq_true, ↓reduceIte, hG01, Nat.le_refl, beq_self_eq_true]
    rw [hPermOut]
    simp only [Nat.reduceSub, wotsChainWalk_succ_steps, wotsChainWalk_zero_steps,
      wotsStepHash_eq_tweak4, Nat.reduceAdd]
  · unfold honestUnaryWotsChainWitness
    have hZ0 : ((3 : Nat) == 0) = false := by decide
    have hZ1 : ¬ ((3 : Nat) ≤ 1) := by decide
    have hZ2 : ¬ ((3 : Nat) ≤ 2) := by decide
    have hG01 : (Goldilocks.zero == Goldilocks.one) = false := by decide
    simp only [hZ0, hZ1, hZ2, Bool.false_eq_true, ↓reduceIte, hG01]
    simp only [Nat.reduceSub, wotsChainWalk_zero_steps]

theorem unaryWotsChainResiduals_allZero_iff
    (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx : Nat)
    (expectedDigit : Goldilocks) (w : UnaryWotsChainWitness)
    (hd : expectedDigit.val < 4) :
    allZeroGoldilocks (unaryWotsChainResiduals pkSeed layer treeIdx kpIdx chainIdx expectedDigit w) = true ↔
      w = honestUnaryWotsChainWitness pkSeed layer treeIdx kpIdx chainIdx expectedDigit.val w.sigVal := by
  unfold unaryWotsChainResiduals
  have hHead6 : ∀ (r0 r1 r2 r3 r4 r5 : Goldilocks),
      allZeroGoldilocks [r0, r1, r2, r3, r4, r5] =
        ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero) && (r2 == Goldilocks.zero) &&
         (r3 == Goldilocks.zero) && (r4 == Goldilocks.zero) && (r5 == Goldilocks.zero)) := by
    intros; simp [allZeroGoldilocks, Bool.and_assoc]
  simp only [allZeroGoldilocks_append, hHead6, Bool.and_eq_true, beq_iff_eq,
    boolBitResidual_eq_zero_iff, gold_sub_eq_zero_iff,
    state12Sub_toList_allZero_iff, poseidon2PermResiduals_allZero_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, hb1⟩, hb2⟩, hm01⟩, hm12⟩, hSum⟩, hIn0⟩, hP0⟩, hMux0⟩,
            hIn1⟩, hP1⟩, hMux1⟩, hIn2⟩, hP2⟩, hMux2⟩
    obtain ⟨ea0, ea1, ea2⟩ := monotone_bits_sum_three_unique hd hb0 hb1 hb2 hm01 hm12 hSum
    have es1 := (muxDigest4Residuals_allZero_iff hb0 _ _ w.s1).mp hMux0
    have es2 := (muxDigest4Residuals_allZero_iff hb1 _ _ w.s2).mp hMux1
    have ee  := (muxDigest4Residuals_allZero_iff hb2 _ _ w.endVal).mp hMux2
    rw [hIn0] at hP0
    rw [hP0, ea0] at es1
    rw [hIn1, es1] at hP1
    rw [hP1, es1, ea1] at es2
    rw [hIn2, es2] at hP2
    rw [hP2, es2, ea2] at ee
    rcases w with ⟨a0, a1, a2, sv, s1, s2, ev, p0, p1, p2⟩
    dsimp only at ea0 ea1 ea2 es1 es2 ee hP0 hP1 hP2
    subst ea0 ea1 ea2 hP0 es1 hP1 es2 hP2 ee
    rfl
  · intro hW
    obtain ⟨sv, hsv⟩ : ∃ sv, sv = w.sigVal := ⟨_, rfl⟩
    rw [← hsv] at hW
    subst hW
    clear hsv
    have hCases : expectedDigit = Goldilocks.zero ∨ expectedDigit = Goldilocks.one ∨
                  expectedDigit = Goldilocks.ofNat 2 ∨ expectedDigit = Goldilocks.ofNat 3 := by
      rcases expectedDigit with ⟨v, hv⟩
      dsimp only at hd
      have hvC : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
      rcases hvC with rfl | rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl (Goldilocks.ext rfl)))
      · exact .inr (.inr (.inr (Goldilocks.ext rfl)))
    have hFlags :
        let hw := honestUnaryWotsChainWitness pkSeed layer treeIdx kpIdx chainIdx expectedDigit.val sv
        (hw.act0 = Goldilocks.zero ∨ hw.act0 = Goldilocks.one) ∧
        (hw.act1 = Goldilocks.zero ∨ hw.act1 = Goldilocks.one) ∧
        (hw.act2 = Goldilocks.zero ∨ hw.act2 = Goldilocks.one) ∧
        Goldilocks.mul hw.act0 (Goldilocks.sub Goldilocks.one hw.act1) = Goldilocks.zero ∧
        Goldilocks.mul hw.act1 (Goldilocks.sub Goldilocks.one hw.act2) = Goldilocks.zero ∧
        Goldilocks.add expectedDigit (Goldilocks.add hw.act0 (Goldilocks.add hw.act1 hw.act2)) =
          Goldilocks.ofNat 3 := by
      dsimp only [honestUnaryWotsChainWitness]
      rcases hCases with rfl | rfl | rfl | rfl <;>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | exact .inl (by decide +kernel) | exact .inr (by decide +kernel) | decide +kernel
    obtain ⟨hb0, hb1, hb2, hm01, hm12, hSum⟩ := hFlags
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, hb1⟩, hb2⟩, hm01⟩, hm12⟩, hSum⟩, rfl⟩, rfl⟩,
            (muxDigest4Residuals_allZero_iff hb0 _ _ _).mpr rfl⟩,
            rfl⟩, rfl⟩, (muxDigest4Residuals_allZero_iff hb1 _ _ _).mpr rfl⟩, rfl⟩, rfl⟩,
            (muxDigest4Residuals_allZero_iff hb2 _ _ _).mpr rfl⟩


module
/-
# Base-4 Digit Extraction, the Anti-Monotone Target Sum, and the Message Representative `mu` (`sig.rs`)

Least-significant-first base-4 digit extraction from 63-bit limbs, the checked WOTS+C digit
vector `extractWotsDigitsChecked` with its constant target sum, the canonical 32-byte to
`Digest5` limb decoding `bytes32ToDigest5`, and the message representative `computeMessageMu`
with the stateful and deterministic-tree `H_msg` sponges.
-/

public import Qsag.Protocol.Aggregation.SuccinctAggregationIop.PackedDigestPrimitives

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv
set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ### Base-4 Digit Extraction, Anti-Monotone Target Sum, and Message Representative `mu` -/

/-- Sum of a list of natural numbers. -/
@[expose] def listNatSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listNatSum xs

/-- Extract `count` base-4 digits (`0..3`), least-significant digit first (`sig.rs:479`). -/
@[expose] def extractLimbBase4Digits : Nat → Nat → List Nat
  | 0, _ => []
  | count + 1, v => (v % 4) :: extractLimbBase4Digits count (v / 4)

/-- Reconstruct an integer from base-4 digits (`d_0 + 4 * d_1 + ...`). -/
@[expose] def evalBase4Digits : List Nat → Nat
  | [] => 0
  | d :: ds => d + 4 * evalBase4Digits ds

theorem extractLimbBase4Digits_length :
    ∀ (count v : Nat), (extractLimbBase4Digits count v).length = count
  | 0, _ => rfl
  | count + 1, v => by
    simp [extractLimbBase4Digits, extractLimbBase4Digits_length count]

theorem extractLimbBase4Digits_all_lt_four :
    ∀ (count v d : Nat), d ∈ extractLimbBase4Digits count v → d < 4
  | 0, _, _, h => by cases h
  | count + 1, v, d, h => by
    rcases List.mem_cons.mp h with rfl | hTail
    · omega
    · exact extractLimbBase4Digits_all_lt_four count (v / 4) d hTail

theorem evalBase4Digits_extractLimbBase4Digits :
    ∀ (count v : Nat),
      evalBase4Digits (extractLimbBase4Digits count v) + (4 ^ count) * (v / (4 ^ count)) = v
  | 0, v => by simp [extractLimbBase4Digits, evalBase4Digits]
  | count + 1, v => by
    have ih := evalBase4Digits_extractLimbBase4Digits count (v / 4)
    have hDiv : (v / 4) / (4 ^ count) = v / (4 ^ (count + 1)) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    have hPow : 4 ^ (count + 1) = 4 * 4 ^ count := by rw [Nat.pow_succ, Nat.mul_comm]
    calc evalBase4Digits (extractLimbBase4Digits (count + 1) v) + (4 ^ (count + 1)) * (v / (4 ^ (count + 1)))
      _ = v % 4 + 4 * evalBase4Digits (extractLimbBase4Digits count (v / 4)) +
            4 * ((4 ^ count) * ((v / 4) / (4 ^ count))) := by
          simp only [extractLimbBase4Digits, evalBase4Digits]
          rw [← hDiv, hPow, Nat.mul_assoc]
      _ = v % 4 + 4 * (evalBase4Digits (extractLimbBase4Digits count (v / 4)) +
            (4 ^ count) * ((v / 4) / (4 ^ count))) := by
          rw [Nat.left_distrib, Nat.add_assoc]
      _ = v % 4 + 4 * (v / 4) := by rw [ih]
      _ = v := Nat.mod_add_div v 4

/-- Wrap-around-free `< 2^63` check on all 5 limbs of `Digest5` (`sig.rs:471`). -/
def checkDigest5Limbs63 (d : Digest5) : Bool :=
  (d.limb0.val < 2 ^ 63) &&
  (d.limb1.val < 2 ^ 63) &&
  (d.limb2.val < 2 ^ 63) &&
  (d.limb3.val < 2 ^ 63) &&
  (d.limb4.val < 2 ^ 63)

/-- Checked extraction of `geom.wotsChains` base-4 digits (`128` at deployed profiles, `sig.rs:470`). -/
def extractWotsDigitsChecked (geom : AggSigGeometry) (d : Digest5) : Option (List Nat) :=
  if checkDigest5Limbs63 d then
    let all128 :=
      extractLimbBase4Digits 31 d.limb0.val ++
      extractLimbBase4Digits 31 d.limb1.val ++
      extractLimbBase4Digits 31 d.limb2.val ++
      extractLimbBase4Digits 31 d.limb3.val ++
      extractLimbBase4Digits 4 d.limb4.val
    some (all128.take geom.wotsChains)
  else
    none

private theorem length_extractAll128 (d : Digest5) :
    (extractLimbBase4Digits 31 d.limb0.val ++
     extractLimbBase4Digits 31 d.limb1.val ++
     extractLimbBase4Digits 31 d.limb2.val ++
     extractLimbBase4Digits 31 d.limb3.val ++
     extractLimbBase4Digits 4 d.limb4.val).length = 128 := by
  simp [extractLimbBase4Digits_length]

theorem extractWotsDigitsChecked_spec {geom : AggSigGeometry} {d : Digest5} {ds : List Nat}
    (hLenLe : geom.wotsChains ≤ 128)
    (hExt : extractWotsDigitsChecked geom d = some ds) :
    ds.length = geom.wotsChains ∧ (∀ x ∈ ds, x < 4) := by
  unfold extractWotsDigitsChecked at hExt
  cases hChk : checkDigest5Limbs63 d
  · simp [hChk] at hExt
  · simp only [hChk, ↓reduceIte, Option.some.injEq] at hExt
    subst hExt
    refine ⟨?_, ?_⟩
    · rw [List.length_take, length_extractAll128]
      omega
    · intro x hx
      have hMem := List.mem_of_mem_take hx
      simp only [List.mem_append] at hMem
      rcases hMem with (((h0 | h1) | h2) | h3) | h4
      · exact extractLimbBase4Digits_all_lt_four 31 _ x h0
      · exact extractLimbBase4Digits_all_lt_four 31 _ x h1
      · exact extractLimbBase4Digits_all_lt_four 31 _ x h2
      · exact extractLimbBase4Digits_all_lt_four 31 _ x h3
      · exact extractLimbBase4Digits_all_lt_four 4 _ x h4

structure SmallerDigitWitness (honest forged : List Nat) where
  idx      : Nat
  hHonest  : idx < honest.length
  hForged  : idx < forged.length
  strictLt : forged[idx]'hForged < honest[idx]'hHonest

/-- Constructive anti-monotonicity: if `forged` and `honest` have equal length,
    `listNatSum forged ≤ listNatSum honest`, and `forged ≠ honest`, locates an explicit chain index `c`
    where **`forged[c] < honest[c]`**! -/
def findSmallerDigitIdx :
    ∀ (honest forged : List Nat),
      honest.length = forged.length →
      listNatSum forged ≤ listNatSum honest →
      forged ≠ honest →
      SmallerDigitWitness honest forged
  | [], [], _, _, hNe => False.elim (hNe rfl)
  | [], _ :: _, hLen, _, _ => False.elim (Nat.succ_ne_zero _ hLen.symm)
  | _ :: _, [], hLen, _, _ => False.elim (Nat.succ_ne_zero _ hLen)
  | xH :: xsH, xF :: xsF, hLen, hSum, hNe =>
    if hLt : xF < xH then
      ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, hLt⟩
    else if hEq : xF = xH then
      have hSubSum : listNatSum xsF ≤ listNatSum xsH := by
        simp only [listNatSum] at hSum
        omega
      have hTailNe : xsF ≠ xsH := fun hT => hNe (by rw [hEq, hT])
      let w := findSmallerDigitIdx xsH xsF (Nat.succ.inj hLen) hSubSum hTailNe
      ⟨w.idx + 1, Nat.succ_lt_succ w.hHonest, Nat.succ_lt_succ w.hForged, w.strictLt⟩
    else
      have hStrictTail : listNatSum xsF < listNatSum xsH := by
        simp only [listNatSum] at hSum
        omega
      have hTailNe : xsF ≠ xsH := fun hT => by rw [hT] at hStrictTail; exact Nat.lt_irrefl _ hStrictTail
      let w := findSmallerDigitIdx xsH xsF (Nat.succ.inj hLen) (Nat.le_of_lt hStrictTail) hTailNe
      ⟨w.idx + 1, Nat.succ_lt_succ w.hHonest, Nat.succ_lt_succ w.hForged, w.strictLt⟩

structure DigitLtThreeWitness (digits : List Nat) where
  idx : Nat
  hIn : idx < digits.length
  lt3 : digits[idx]'hIn < 3

/-- Constructive search for a chain index with `digits[c] < 3` whenever `listNatSum digits < 3 * digits.length`. -/
def findDigitLtThreeIdx :
    ∀ (digits : List Nat),
      listNatSum digits < 3 * digits.length →
      DigitLtThreeWitness digits
  | [], hSum => False.elim (by simp [listNatSum] at hSum)
  | d :: ds, hSum =>
    if hLt : d < 3 then
      ⟨0, Nat.zero_lt_succ _, hLt⟩
    else
      have hTail : listNatSum ds < 3 * ds.length := by
        simp only [listNatSum, List.length_cons] at hSum
        omega
      let w := findDigitLtThreeIdx ds hTail
      ⟨w.idx + 1, Nat.succ_lt_succ w.hIn, w.lt3⟩

/-- Pack 32 bytes losslessly into 5 canonical `< 2^56` / `< 2^32` Goldilocks limbs (`bytes32_to_limbs56`). -/
@[expose] def bytes32ToDigest5 (bs : List UInt8) : Digest5 :=
  let b := (bs ++ List.replicate (32 - bs.length) (0 : UInt8)).take 32
  let l0 := ofBE (b.take 7)
  let l1 := ofBE ((b.drop 7).take 7)
  let l2 := ofBE ((b.drop 14).take 7)
  let l3 := ofBE ((b.drop 21).take 7)
  let l4 := ofBE ((b.drop 28).take 4)
  have h7 : ∀ xs : List UInt8, xs.length ≤ 7 → ofBE xs < goldilocksPrime := fun xs hx => by
    have hLt := ofBE_lt xs
    have hPow : 256 ^ xs.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) hx
    exact Nat.lt_of_lt_of_le hLt (Nat.le_trans hPow (by decide))
  have h4 : ∀ xs : List UInt8, xs.length ≤ 4 → ofBE xs < goldilocksPrime := fun xs hx => by
    have hLt := ofBE_lt xs
    have hPow : 256 ^ xs.length ≤ 256 ^ 4 := Nat.pow_le_pow_right (by decide) hx
    exact Nat.lt_of_lt_of_le hLt (Nat.le_trans hPow (by decide))
  { limb0 := ⟨l0, h7 _ (List.length_take_le _ _)⟩
    limb1 := ⟨l1, h7 _ (List.length_take_le _ _)⟩
    limb2 := ⟨l2, h7 _ (List.length_take_le _ _)⟩
    limb3 := ⟨l3, h7 _ (List.length_take_le _ _)⟩
    limb4 := ⟨l4, h4 _ (List.length_take_le _ _)⟩ }

/-- Canonical byte serialization of `AggValidatorPk` (`65` bytes). -/
def encodeAggValidatorPkBytes (pk : AggValidatorPk) : List UInt8 :=
  let profByte : UInt8 := match pk.profile with
    | .xmssPoseidon2 => 1
    | .corduroyPoseidon2 => 2
  profByte ::
    be 8 pk.pkSeed.x0.val ++ be 8 pk.pkSeed.x1.val ++ be 8 pk.pkSeed.x2.val ++ be 8 pk.pkSeed.x3.val ++
    be 8 pk.pkRoot.x0.val ++ be 8 pk.pkRoot.x1.val ++ be 8 pk.pkRoot.x2.val ++ be 8 pk.pkRoot.x3.val

/-- ASCII byte tag `"QSAG.MU/v2"` (`0x51 0x53 0x41 0x47 0x2e 0x4d 0x55 0x2f 0x76 0x32`). -/
def qsagMuTagBytes : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x4d, 0x55, 0x2f, 0x76, 0x32]

/-- Domain-framed 5-limb message representative `mu` (`compute_message_mu` in `sig.rs:260`). -/
@[expose] def computeMessageMu (pk : AggValidatorPk) (msg : List UInt8) : Digest5 :=
  let framed := encodeMultiFrame [qsagMuTagBytes, encodeAggValidatorPkBytes pk, msg]
  bytes32ToDigest5 (poseidon2Hash32 framed)

/-- Stateful layer-0 randomized message hash `compute_hmsg_stateful` (`sig.rs:396`). -/
def computeHmsgStateful (pk : AggValidatorPk) (rRand : Digest4) (mu : Digest5)
    (kpIdx tswCtr : Nat) : Digest5 :=
  let kpCtr := Goldilocks.ofNat ((kpIdx % (2 ^ 32)) * (2 ^ 32) + (tswCtr % (2 ^ 32)))
  let st0 := poseidon2Perm12
    ⟨pk.pkSeed,
     pk.pkRoot,
     ⟨domainHMsgStateful, kpCtr, mu.limb4, poseidon2IvTag⟩⟩
  let muLow : Digest4 := ⟨mu.limb0, mu.limb1, mu.limb2, mu.limb3⟩
  let st1 := poseidon2Perm12 ⟨lane4Add st0.b0 rRand, lane4Add st0.b1 muLow, st0.b2⟩
  let st2 := poseidon2Perm12
    ⟨⟨Goldilocks.add st1.b0.x0 Goldilocks.one, st1.b0.x1, st1.b0.x2, st1.b0.x3⟩,
     st1.b1, st1.b2⟩
  { limb0 := st2.b0.x0
    limb1 := st2.b0.x1
    limb2 := st2.b0.x2
    limb3 := st2.b0.x3
    limb4 := st2.b1.x0 }

/-- Deterministic `rRand`-free & `mu`-free tree `H_msg` (`compute_hmsg_det_tree` in `sig.rs:433`). -/
def computeHmsgDetTree (pk : AggValidatorPk) (layer treeIdx kpIdx tswCtr : Nat)
    (childOrForsRoot : Digest4) : Digest5 :=
  let layerKp := Goldilocks.ofNat ((layer % (2 ^ 32)) * (2 ^ 32) + (kpIdx % (2 ^ 32)))
  let st0 := poseidon2Perm12
    ⟨pk.pkSeed,
     pk.pkRoot,
     ⟨domainHMsgDetTree,
      layerKp,
      Goldilocks.ofNat (treeIdx % (2 ^ 32)),
      Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩
  let b0' := lane4Add st0.b0 childOrForsRoot
  let b1' : Digest4 :=
    ⟨Goldilocks.add st0.b1.x0 (Goldilocks.ofNat (tswCtr % (2 ^ 32))),
     Goldilocks.add st0.b1.x1 Goldilocks.one,
     st0.b1.x2,
     st0.b1.x3⟩
  let st1 := poseidon2Perm12 ⟨b0', b1', st0.b2⟩
  { limb0 := st1.b0.x0
    limb1 := st1.b0.x1
    limb2 := st1.b0.x2
    limb3 := st1.b0.x3
    limb4 := st1.b1.x0 }

end Qsag

end

public section

namespace Qsag

theorem extractLimbBase4Digits_zero (v : Nat) : extractLimbBase4Digits 0 v = [] := by rfl
theorem extractLimbBase4Digits_succ (n v : Nat) :
    extractLimbBase4Digits (n + 1) v = v % 4 :: extractLimbBase4Digits n (v / 4) := by rfl
theorem evalBase4Digits_nil : evalBase4Digits [] = 0 := by rfl
theorem evalBase4Digits_cons (d : Nat) (ds : List Nat) :
    evalBase4Digits (d :: ds) = d + 4 * evalBase4Digits ds := by rfl
end Qsag

end

public section

namespace Qsag

#export_eqns checkDigest5Limbs63
#export_eqns extractWotsDigitsChecked
#export_eqns listNatSum
#export_eqns computeHmsgStateful computeHmsgDetTree
end Qsag

end

public section

namespace Qsag

theorem bytes32ToDigest5_limbs (bs : List UInt8) :
    let b := (bs ++ List.replicate (32 - bs.length) (0 : UInt8)).take 32
    bytes32ToDigest5 bs =
      ⟨Goldilocks.ofNat (ofBE (b.take 7)),
       Goldilocks.ofNat (ofBE ((b.drop 7).take 7)),
       Goldilocks.ofNat (ofBE ((b.drop 14).take 7)),
       Goldilocks.ofNat (ofBE ((b.drop 21).take 7)),
       Goldilocks.ofNat (ofBE ((b.drop 28).take 4))⟩ := by
  dsimp only
  have h7 : ∀ xs : List UInt8, xs.length ≤ 7 → ofBE xs < goldilocksPrime := fun xs hx =>
    Nat.lt_of_lt_of_le (ofBE_lt xs)
      (Nat.le_trans (Nat.pow_le_pow_right (by decide) hx) (by decide))
  have h4 : ∀ xs : List UInt8, xs.length ≤ 4 → ofBE xs < goldilocksPrime := fun xs hx =>
    Nat.lt_of_lt_of_le (ofBE_lt xs)
      (Nat.le_trans (Nat.pow_le_pow_right (by decide) hx) (by decide))
  unfold bytes32ToDigest5
  dsimp only
  congr 1
  · exact Goldilocks.ext (Nat.mod_eq_of_lt (h7 _ (List.length_take_le _ _))).symm
  · exact Goldilocks.ext (Nat.mod_eq_of_lt (h7 _ (List.length_take_le _ _))).symm
  · exact Goldilocks.ext (Nat.mod_eq_of_lt (h7 _ (List.length_take_le _ _))).symm
  · exact Goldilocks.ext (Nat.mod_eq_of_lt (h7 _ (List.length_take_le _ _))).symm
  · exact Goldilocks.ext (Nat.mod_eq_of_lt (h4 _ (List.length_take_le _ _))).symm

theorem computeHmsgStateful_xmss_eq (pkSeed pkRoot rRand : Digest4)
    (msg : List UInt8) (kpIdx tswCtr : Nat) :
    let h := compactJortsHmsgStateful pkSeed pkRoot rRand msg kpIdx tswCtr
    computeHmsgStateful ⟨.xmssPoseidon2, pkSeed, pkRoot⟩ rRand
        (computeMessageMu ⟨.xmssPoseidon2, pkSeed, pkRoot⟩ msg) kpIdx tswCtr =
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ := by
  dsimp only
  unfold computeMessageMu encodeAggValidatorPkBytes qsagMuTagBytes
  dsimp only
  rw [bytes32ToDigest5_limbs]
  unfold computeHmsgStateful
  simp only [domainHMsgStateful.public_eqs, poseidon2IvTag.public_eqs]
  rw [compactJortsHmsgStateful_eq_def]

theorem extractWotsDigitsChecked_compactAuditGeom (d : Digest5) :
    extractWotsDigitsChecked compactAuditGeom d =
      if checkDigest5Limbs63 d then
        some [d.limb0.val % 4, (d.limb0.val / 4) % 4]
      else none := by
  unfold extractWotsDigitsChecked
  rw [compactAuditGeom.public_eq_1]
  dsimp only
  cases checkDigest5Limbs63 d <;> rfl

end Qsag
end

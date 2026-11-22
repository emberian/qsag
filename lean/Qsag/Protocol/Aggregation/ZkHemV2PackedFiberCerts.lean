module
/-
# Qsag.Protocol.Aggregation.ZkHemV2PackedFiberCerts — Packed-Fiber WHIR Schedule Certificates, Single-OOD `< 2^{-277}` Sampler & Recursive Margin Schedule (`< 2^{-128}`)

Closes the schedule-certificate obligations for `zkHemV2ProdSched` (`16 ≤ logCells ≤ 28`) and establishes
both single-proof packed-fiber `< 2^{-128}` QROM soundness and `[DKT26]` recursive-tree `< 2^{-128}` QROM
soundness up to depth `d ≤ 16` (`65,536` leaf shards, `131,071` tree nodes) at `Q ≤ 2^{64}`:
1. **Packed-Fiber Merkle Depth (`packedStageDepth`):** Certifies that deployed fiber trees have depth
   `st.logDomain` (not scalar `st.logDomain + st.foldK`), accepting honest `st.logDomain`-length Canopy
   openings across all 45 stage entries while `scalarStageDepth` rejects them (`#tooth_pair`).
2. **Constructive 400-Bit `QuinticGoldilocks` Sampler (`decodeQuintic400`) & Single-OOD `< 2^{-277}` Budget:**
   Proves `decodeQuintic400_preimage_le` (`≤ 2^400 / p^5 + 1` seed preimages per `𝔽_{p^5}` element) and
   `deployed_single_ood_gs_bad_lt_277`, bounding Guruswami–Sudan decode-list pair collisions on a single
   400-bit OOD squeeze strictly below `< 2^{-277}` across all 45 stage entries of `16 ≤ logCells ≤ 28`
   with positive integer seed budgets (`≥ 1` seed) at every round.
3. **All 13 Deployed Packed-Fiber Schedules Clear `< 2^{-128}` (`zkHemV2_packed_all13_qrom_lt_128_at_2pow64`):**
   Proves `< 2^{-128}` at `Q ≤ 2^{64}` across `16 ≤ logCells ≤ 28` under both 400-bit `TurboSHAKE256`
   (`.turboShake400`) and 448-bit `Poseidon2-GL-w24` (`.poseidon2Gl24`, `p^7 > 2^447`) commitments.
4. **Recursive `[DKT26]` Margin Schedule (`zkHemV2RecursiveMarginSched`):** Proves `< 2^{-128}` across
   all `d ≤ 16` (`≤ 131,071` tree nodes) at `Q ≤ 2^{64}`, paired with `#tooth_pair` showing why
   single-proof `q_0 = 267` overflows `2^{-128}` when summed across `131,071` tree nodes.
-/

public import Qsag.Math.Poseidon2Gl24
public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Protocol.Aggregation.ClosedWhirSchedule
public import Qsag.Protocol.Aggregation.ZkHemV2
public import Qsag.Protocol.Aggregation.ZkHemV2ScheduleCert
import Qsag.Math.PolyRing
import Qsag.Coding.GuruswamiSudan
import Qsag.Tactic.AssuranceKit

public section
attribute [-instance] Fin.instLinearOrderPackage

namespace Qsag.ZkHemV2Packed

open Qsag Qsag.ClosedFs Qsag.ClosedWhir Qsag.ZkHemV2Cert

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 100000

local infixl:65 " +ᵍ " => CommRingOps.add
local infixl:65 " -ᵍ " => CommRingOps.sub
local infixl:70 " *ᵍ " => CommRingOps.mul

/-! ## §1. 400-Bit `TurboSHAKE256` & 448-Bit `Poseidon2-GL-w24` QROM Commitment Profiles -/

/-- Deployed post-quantum Merkle commitment profiles for succinct WHIR and recursive IVC. -/
inductive WhirCommitmentProfile where
  | turboShake400
  | poseidon2Gl24
  deriving DecidableEq, Repr

/-- Exact cardinality `p^7` of 7-limb `Poseidon2-GL-w24` digests (`Digest7`). -/
@[expose] def poseidon2Gl24DigestCard : Nat := goldilocksPrime ^ 7

theorem poseidon2Gl24DigestCard_pos : 0 < poseidon2Gl24DigestCard := by decide +kernel

theorem poseidon2Gl24DigestCard_gt_2pow447 :
    2 ^ 447 < poseidon2Gl24DigestCard ∧ 2 ^ 400 < poseidon2Gl24DigestCard := by
  unfold poseidon2Gl24DigestCard
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- QROM multi-collision / preimage bound (`6680 · Q^3 / |Digest|`) for `WhirCommitmentProfile`. -/
@[expose] def merkleProfileQromBound (prof : WhirCommitmentProfile) (Q : Nat) : RatBound :=
  match prof with
  | .turboShake400 => merkle400QromBound Q
  | .poseidon2Gl24 => ⟨6680 * Q ^ 3, poseidon2Gl24DigestCard, poseidon2Gl24DigestCard_pos⟩

theorem merkleProfileQromBound_le_400 (prof : WhirCommitmentProfile) (Q : Nat) :
    RatBound.le (merkleProfileQromBound prof Q) (merkle400QromBound Q) := by
  cases prof with
  | turboShake400 => exact RatBound.le_refl _
  | poseidon2Gl24 =>
    show 6680 * Q ^ 3 * 2 ^ 400 ≤ 6680 * Q ^ 3 * poseidon2Gl24DigestCard
    exact Nat.mul_le_mul_left _ (Nat.le_of_lt poseidon2Gl24DigestCard_gt_2pow447.2)

theorem merkleProfileQromBound_mono (prof : WhirCommitmentProfile) {Q Q' : Nat} (h : Q ≤ Q') :
    RatBound.le (merkleProfileQromBound prof Q) (merkleProfileQromBound prof Q') := by
  cases prof with
  | turboShake400 => exact merkle400QromBound_mono h
  | poseidon2Gl24 =>
    show 6680 * Q ^ 3 * poseidon2Gl24DigestCard ≤ 6680 * Q' ^ 3 * poseidon2Gl24DigestCard
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6680 (Nat.pow_le_pow_left h 3))

/-- Concrete `MerkleSetup` instantiated with 1-call `Poseidon2-GL-w24` Jive compression (`rate = 16`). -/
def poseidon2Gl24MerkleSetup {Leaf : Type} (leafHash : Nat → Nat → Leaf → Poseidon2Gl24.Digest7) :
    MerkleSetup Poseidon2Gl24.Digest7 Leaf where
  node := fun lvl idx l r =>
    Poseidon2Gl24.poseidon2Gl24CompressMerkle l r (Goldilocks.ofNat lvl) (Goldilocks.ofNat idx)
  leaf := leafHash

theorem ratBound_lt_of_le_of_lt_packed {a b c : RatBound}
    (hab : RatBound.le a b) (hbc : RatBound.lt b c) : RatBound.lt a c := by
  have h1 : a.num * b.den * c.den ≤ b.num * a.den * c.den := Nat.mul_le_mul_right c.den hab
  have h2 : a.den * (b.num * c.den) < a.den * (c.num * b.den) := by
    rw [Nat.mul_comm a.den _, Nat.mul_comm a.den _]
    exact nat_mul_lt_mul_right' hbc a.h_pos
  have e1 : b.num * a.den * c.den = a.den * (b.num * c.den) := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have e2 : a.den * (c.num * b.den) = a.den * c.num * b.den := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have e0 : a.num * b.den * c.den = a.num * c.den * b.den := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have h3 : a.num * c.den * b.den < a.den * c.num * b.den := by
    rw [← e0, ← e2]; rw [e1] at h1; exact Nat.lt_of_le_of_lt h1 h2
  have h4 := nat_lt_of_mul_lt_mul_right' h3
  rwa [Nat.mul_comm a.den c.num] at h4

/-! ## §2. Constructive 400-Bit `QuinticGoldilocks` Sampler & Preimage Bound -/

/-- Canonical base-`p` mixed-radix encoding `QuinticGoldilocks → Fin (p^5)`. -/
def encodeQuinticNat (z : QuinticGoldilocks) : Nat :=
  let p := goldilocksPrime
  z.c0.val + p * (z.c1.val + p * (z.c2.val + p * (z.c3.val + p * z.c4.val)))

/-- Canonical base-`p` mixed-radix decoding `Nat → QuinticGoldilocks`. -/
def decodeQuinticNat (n : Nat) : QuinticGoldilocks :=
  let p := goldilocksPrime
  let hp : 0 < p := by decide
  ⟨⟨n % p, Nat.mod_lt _ hp⟩,
   ⟨(n / p) % p, Nat.mod_lt _ hp⟩,
   ⟨(n / (p * p)) % p, Nat.mod_lt _ hp⟩,
   ⟨(n / (p * (p * p))) % p, Nat.mod_lt _ hp⟩,
   ⟨(n / (p * (p * (p * p)))) % p, Nat.mod_lt _ hp⟩⟩

/-- 400-bit Fiat–Shamir squeeze into `QuinticGoldilocks` (`𝔽_{p^5}`). -/
def decodeQuintic400 (c : Nat) : QuinticGoldilocks :=
  decodeQuinticNat (c % quinticGoldilocksCard)

private theorem mixed_radix_lt {p a b k : Nat} (ha : a < p) (hb : b < k) :
    a + p * b < p * k := by
  have h1 : b + 1 ≤ k := hb
  calc a + p * b < p + p * b := Nat.add_lt_add_right ha _
    _ = p * (b + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    _ ≤ p * k := Nat.mul_le_mul_left p h1

theorem encodeQuinticNat_lt (z : QuinticGoldilocks) :
    encodeQuinticNat z < quinticGoldilocksCard := by
  unfold encodeQuinticNat quinticGoldilocksCard
  have h4 : z.c4.val < goldilocksPrime * 1 := by rw [Nat.mul_one]; exact z.c4.isLt
  have h3 := mixed_radix_lt z.c3.isLt h4
  have h2 := mixed_radix_lt z.c2.isLt h3
  have h1 := mixed_radix_lt z.c1.isLt h2
  have h0 := mixed_radix_lt z.c0.isLt h1
  simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] using h0

theorem encodeQuinticNat_decodeQuinticNat {n : Nat} (hn : n < quinticGoldilocksCard) :
    encodeQuinticNat (decodeQuinticNat n) = n := by
  unfold encodeQuinticNat decodeQuinticNat
  dsimp only
  let p := goldilocksPrime
  have hn5 : n < p * (p * (p * (p * p))) := by
    simpa only [quinticGoldilocksCard, Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc] using hn
  let q1 := n / p
  let q2 := q1 / p
  let q3 := q2 / p
  let q4 := q3 / p
  have eq1 : q1 = n / p := rfl
  have eq2 : q2 = n / (p * p) := by dsimp only [q2, q1]; rw [Nat.div_div_eq_div_mul]
  have eq3 : q3 = n / (p * (p * p)) := by
    dsimp only [q3]; rw [eq2, Nat.div_div_eq_div_mul, Nat.mul_comm (p * p) p]
  have eq4 : q4 = n / (p * (p * (p * p))) := by
    dsimp only [q4]; rw [eq3, Nat.div_div_eq_div_mul, Nat.mul_comm (p * (p * p)) p]
  have hq4Lt : q4 < p := by
    rw [eq4]
    let M := p * (p * (p * p))
    rcases Nat.lt_or_ge (n / M) p with hLt | hGe
    · exact hLt
    · exfalso
      have h1 : M * p ≤ M * (n / M) := Nat.mul_le_mul_left M hGe
      have h2 : M * (n / M) ≤ M * (n / M) + n % M := Nat.le_add_right _ _
      have h3 : M * (n / M) + n % M = n := Nat.div_add_mod n M
      have h4 : p * M ≤ n := by rw [Nat.mul_comm p M, ← h3]; exact Nat.le_trans h1 h2
      have hnM : n < p * M := hn5
      exact Nat.not_le_of_gt hnM h4
  rw [← eq1, ← eq2, ← eq3, ← eq4, Nat.mod_eq_of_lt hq4Lt]
  have s3 : q3 % p + p * q4 = q3 := by rw [Nat.add_comm]; exact Nat.div_add_mod q3 p
  have s2 : q2 % p + p * q3 = q2 := by rw [Nat.add_comm]; exact Nat.div_add_mod q2 p
  have s1 : q1 % p + p * q2 = q1 := by rw [Nat.add_comm]; exact Nat.div_add_mod q1 p
  have s0 : n % p + p * q1 = n := by rw [Nat.add_comm]; exact Nat.div_add_mod n p
  rw [s3, s2, s1, s0]

theorem decodeQuinticNat_encodeQuinticNat (z : QuinticGoldilocks) :
    decodeQuinticNat (encodeQuinticNat z) = z := by
  unfold decodeQuinticNat encodeQuinticNat; dsimp only
  let p := goldilocksPrime
  have hp : 0 < p := by decide
  let s3 := z.c3.val + p * z.c4.val; let s2 := z.c2.val + p * s3; let s1 := z.c1.val + p * s2
  have d1 : (z.c0.val + p * s1) / p = s1 := by
    rw [Nat.add_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt z.c0.isLt, Nat.add_zero]
  have m0 : (z.c0.val + p * s1) % p = z.c0.val := by
    rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt z.c0.isLt]
  have d2 : (z.c0.val + p * s1) / (p * p) = s2 := by
    rw [← Nat.div_div_eq_div_mul, d1]; dsimp only [s1]; rw [Nat.add_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt z.c1.isLt, Nat.add_zero]
  have m1 : ((z.c0.val + p * s1) / p) % p = z.c1.val := by
    rw [d1]; dsimp only [s1]; rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt z.c1.isLt]
  have d3 : (z.c0.val + p * s1) / (p * (p * p)) = s3 := by
    rw [Nat.mul_comm p (p * p), ← Nat.div_div_eq_div_mul, d2]; dsimp only [s2]; rw [Nat.add_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt z.c2.isLt, Nat.add_zero]
  have m2 : ((z.c0.val + p * s1) / (p * p)) % p = z.c2.val := by
    rw [d2]; dsimp only [s2]; rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt z.c2.isLt]
  have d4 : (z.c0.val + p * s1) / (p * (p * (p * p))) = z.c4.val := by
    rw [Nat.mul_comm p (p * (p * p)), ← Nat.div_div_eq_div_mul, d3]; dsimp only [s3]; rw [Nat.add_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt z.c3.isLt, Nat.add_zero]
  have m3 : ((z.c0.val + p * s1) / (p * (p * p))) % p = z.c3.val := by
    rw [d3]; dsimp only [s3]; rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt z.c3.isLt]
  have m4 : ((z.c0.val + p * s1) / (p * (p * (p * p)))) % p = z.c4.val := by
    rw [d4, Nat.mod_eq_of_lt z.c4.isLt]
  exact QuinticGoldilocks.ext (Goldilocks.ext m0) (Goldilocks.ext m1)
    (Goldilocks.ext m2) (Goldilocks.ext m3) (Goldilocks.ext m4)

theorem qsum_split_add_p :
    ∀ (a : Nat) (f : Nat → Nat) (b : Nat),
      qsum (a + b) (fun i => f i.1) =
        qsum a (fun i => f i.1) + qsum b (fun j => f (a + j.1))
  | 0, f, b => by
    rw [Nat.zero_add, qsum_zero, Nat.zero_add]
    exact qsum_congr (fun j => by rw [Nat.zero_add])
  | a + 1, f, b => by
    rw [Nat.succ_add, qsum_succ, qsum_succ]
    dsimp only
    rw [qsum_split_add_p a (fun k => f (k + 1)) b, ← Nat.add_assoc]
    refine congrArg (f 0 + qsum a _ + ·) ?_
    exact qsum_congr (fun j => by rw [Nat.succ_add, Nat.add_succ])

theorem qsum_append_one (n : Nat) (f : Nat → Nat) :
    qsum (n + 1) (fun i => f i.1) = qsum n (fun i => f i.1) + f n := by
  rw [qsum_split_add_p n f 1, qsum_succ, qsum_zero, Nat.add_zero, Nat.add_zero]

private theorem qsum_le_extend {a b : Nat} (h : a ≤ b) (f : Nat → Nat) :
    qsum a (fun i => f i.1) ≤ qsum b (fun i => f i.1) := by
  have hb : b = a + (b - a) := (Nat.add_sub_of_le h).symm
  rw [hb, qsum_split_add_p a f (b - a)]
  exact Nat.le_add_right _ _

private theorem qsum_single_hit_le_one (M r : Nat) :
    qsum M (fun j => if j.1 = r then 1 else 0) ≤ 1 := by
  if hr : r < M then
    have hEq := qsum_ite_eq M ⟨r, hr⟩ 1
    have hCongr : qsum M (fun j => if j.1 = r then 1 else 0) =
        qsum M (fun j => if j = ⟨r, hr⟩ then 1 else 0) :=
      qsum_congr (fun j => by
        by_cases hj : j = ⟨r, hr⟩
        · subst hj; simp
        · have hjv : j.1 ≠ r := fun hv => hj (Fin.ext hv)
          simp [hj, hjv])
    rw [hCongr, hEq]; exact Nat.le_refl 1
  else
    have hZ : ∀ j : Fin M, (if j.1 = r then 1 else 0) = 0 := fun j => by
      have hne : j.1 ≠ r := by omega
      simp [hne]
    rw [qsum_congr hZ, qsum_const, Nat.mul_zero]; exact Nat.zero_le 1

private theorem qsum_mod_blocks_le (M r : Nat) :
    ∀ K : Nat, qsum (K * M) (fun c => if c.1 % M = r then 1 else 0) ≤ K
  | 0 => by rw [Nat.zero_mul, qsum_zero]; exact Nat.le_refl 0
  | K + 1 => by
    have hSplit := qsum_split_add_p (K * M) (fun u => if u % M = r then 1 else 0) M
    rw [Nat.succ_mul, hSplit]
    have ih := qsum_mod_blocks_le M r K
    have hTail : qsum M (fun j => if (K * M + j.1) % M = r then 1 else 0) ≤ 1 := by
      have hCongr : qsum M (fun j => if (K * M + j.1) % M = r then 1 else 0) =
          qsum M (fun j => if j.1 = r then 1 else 0) :=
        qsum_congr (fun j => by
          rw [Nat.add_comm (K * M) j.1, Nat.mul_comm K M, Nat.add_mul_mod_self_left,
              Nat.mod_eq_of_lt j.2])
      rw [hCongr]; exact qsum_single_hit_le_one M r
    exact Nat.add_le_add ih hTail

/-- **Constructive 400-Bit Sampler Preimage Bound (`decodeQuintic400_preimage_le`):**
    Every `z : QuinticGoldilocks` has at most `N / p^5 + 1` seed preimages in `Fin N`. -/
theorem decodeQuintic400_preimage_le (N : Nat) (z : QuinticGoldilocks) :
    qsum N (fun c => if decodeQuintic400 c.1 = z then 1 else 0) ≤
      N / quinticGoldilocksCard + 1 := by
  let M := quinticGoldilocksCard
  have hM : 0 < M := quinticGoldilocksCard_pos
  have hNLe : N ≤ (N / M + 1) * M := by
    have hDiv := Nat.div_add_mod N M
    have hMod := Nat.mod_lt N hM
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (N / M) M]
    omega
  have hImp : ∀ c : Fin N,
      (if decodeQuintic400 c.1 = z then 1 else 0) ≤
      (if c.1 % M = encodeQuinticNat z then 1 else 0) := by
    intro c
    if hEq : decodeQuintic400 c.1 = z then
      have hCode : c.1 % M = encodeQuinticNat z := by
        rw [← hEq]; unfold decodeQuintic400
        exact (encodeQuinticNat_decodeQuinticNat (Nat.mod_lt c.1 hM)).symm
      simp [hEq, hCode]
    else
      simp [hEq]
  exact Nat.le_trans (qsum_le_qsum hImp)
    (Nat.le_trans (qsum_le_extend hNLe (fun k => if k % M = encodeQuinticNat z then 1 else 0))
      (qsum_mod_blocks_le M (encodeQuinticNat z) (N / M + 1)))

/-! ## §3. Single-OOD Polynomial Root & GS Decode-List Collision Bounds (`< 2^{-277}`) -/

private def polyQuotAt (z : QuinticGoldilocks) : List QuinticGoldilocks → List QuinticGoldilocks
  | [] => []
  | [_] => []
  | _ :: b :: rest =>
    RoundPoly.evalCoeffs (b :: rest) z :: polyQuotAt z (b :: rest)

private theorem polyQuotAt_length (z : QuinticGoldilocks) :
    ∀ p : List QuinticGoldilocks, (polyQuotAt z p).length = p.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: b :: rest => by
    show (polyQuotAt z (b :: rest)).length + 1 = (b :: rest).length
    rw [polyQuotAt_length z (b :: rest)]
    simp only [List.length_cons, Nat.add_sub_cancel]

private theorem evalCoeffs_decomp_at (z x : QuinticGoldilocks) :
    ∀ p : List QuinticGoldilocks,
      RoundPoly.evalCoeffs p x =
        RoundPoly.evalCoeffs p z +ᵍ (x -ᵍ z) *ᵍ RoundPoly.evalCoeffs (polyQuotAt z p) x
  | [] => by simp only [polyQuotAt, RoundPoly.evalCoeffs]; constructive_ring
  | [a] => by
    simp only [polyQuotAt, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil]
    constructive_ring
  | a :: b :: rest => by
    have ih := evalCoeffs_decomp_at z x (b :: rest)
    change a +ᵍ x *ᵍ RoundPoly.evalCoeffs (b :: rest) x =
      (a +ᵍ z *ᵍ RoundPoly.evalCoeffs (b :: rest) z) +ᵍ
      (x -ᵍ z) *ᵍ (RoundPoly.evalCoeffs (b :: rest) z +ᵍ
        x *ᵍ RoundPoly.evalCoeffs (polyQuotAt z (b :: rest)) x)
    rw [ih]
    constructive_ring

private def polyInsertAt (z r : QuinticGoldilocks) : List QuinticGoldilocks → List QuinticGoldilocks
  | [] => [r]
  | c :: cs => (r -ᵍ z *ᵍ c) :: polyInsertAt z c cs

private theorem polyInsertAt_quot (z : QuinticGoldilocks) :
    ∀ (p : List QuinticGoldilocks), p ≠ [] →
      polyInsertAt z (RoundPoly.evalCoeffs p z) (polyQuotAt z p) = p
  | [], h => absurd rfl h
  | [a], _ => by
    simp only [polyQuotAt, polyInsertAt, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | a :: b :: rest, _ => by
    have ih := polyInsertAt_quot z (b :: rest) (List.cons_ne_nil b rest)
    change (RoundPoly.evalCoeffs (a :: b :: rest) z -ᵍ z *ᵍ RoundPoly.evalCoeffs (b :: rest) z) ::
      polyInsertAt z (RoundPoly.evalCoeffs (b :: rest) z) (polyQuotAt z (b :: rest)) =
      a :: b :: rest
    rw [ih]; congr 1
    simp only [RoundPoly.evalCoeffs_cons]
    constructive_ring

private def allZeroCoeffs : List QuinticGoldilocks → Bool
  | [] => true
  | c :: cs => decide (c = CommRingOps.zero) && allZeroCoeffs cs

private theorem polyInsertAt_allZero (z : QuinticGoldilocks) :
    ∀ (q : List QuinticGoldilocks), allZeroCoeffs q = true →
      ∀ (r : QuinticGoldilocks), r = CommRingOps.zero →
        allZeroCoeffs (polyInsertAt z r q) = true
  | [], _, r, hr => by subst hr; simp [polyInsertAt, allZeroCoeffs]
  | c :: cs, hq, r, hr => by
    subst hr
    rw [allZeroCoeffs, Bool.and_eq_true] at hq
    have hc : c = CommRingOps.zero := of_decide_eq_true hq.1
    subst hc
    have hDiff : (CommRingOps.zero -ᵍ z *ᵍ CommRingOps.zero) = CommRingOps.zero := by
      constructive_ring
    simp only [polyInsertAt, allZeroCoeffs, hDiff, decide_true, Bool.true_and]
    exact polyInsertAt_allZero z cs hq.2 CommRingOps.zero rfl

private theorem nonzero_poly_seed_roots_le (N : Nat) :
    ∀ (d : Nat) (p : List QuinticGoldilocks),
      p.length ≤ d + 1 → allZeroCoeffs p = false →
      qsum N (fun c =>
        if RoundPoly.evalCoeffs p (decodeQuintic400 c.1) = CommRingOps.zero then 1 else 0) ≤
        d * (N / quinticGoldilocksCard + 1)
  | 0, p, hLen, hNz => by
    rcases p with _ | ⟨a, _ | _⟩
    · cases hNz
    · simp only [allZeroCoeffs, Bool.and_true] at hNz
      have ha : a ≠ CommRingOps.zero := fun he => by rw [decide_eq_true he] at hNz; cases hNz
      have hZ : ∀ c : Fin N,
          (if RoundPoly.evalCoeffs [a] (decodeQuintic400 c.1) = CommRingOps.zero then 1 else 0) = 0 := by
        intro c
        have hEv : RoundPoly.evalCoeffs [a] (decodeQuintic400 c.1) = a := by
          simp only [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil,
            LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
        rw [hEv]; simp [ha]
      rw [qsum_congr hZ, qsum_const, Nat.mul_zero, Nat.zero_mul]; exact Nat.le_refl 0
    · simp only [List.length_cons] at hLen; omega
  | d + 1, p, hLen, hNz => by
    let hit (u : Nat) : Bool :=
      decide (RoundPoly.evalCoeffs p (decodeQuintic400 u) = CommRingOps.zero)
    cases hFind : (List.range N).find? hit with
    | none =>
      have hZ : ∀ c : Fin N,
          (if RoundPoly.evalCoeffs p (decodeQuintic400 c.1) = CommRingOps.zero then 1 else 0) = 0 := by
        intro c
        have hFalse := List.find?_eq_none.mp hFind c.1 (List.mem_range.mpr c.2)
        have hNe : RoundPoly.evalCoeffs p (decodeQuintic400 c.1) ≠ CommRingOps.zero := fun he => by
          dsimp only [hit] at hFalse; rw [decide_eq_true he] at hFalse; exact hFalse rfl
        simp [hNe]
      rw [qsum_congr hZ, qsum_const, Nat.mul_zero]; exact Nat.zero_le _
    | some u0 =>
      have hHit0 : hit u0 = true := List.find?_some (p := hit) hFind
      have hRoot0 : RoundPoly.evalCoeffs p (decodeQuintic400 u0) = CommRingOps.zero :=
        of_decide_eq_true hHit0
      let z0 := decodeQuintic400 u0
      have hpNe : p ≠ [] := fun he => by subst he; cases hNz
      let qt := polyQuotAt z0 p
      have hQtLen : qt.length ≤ d + 1 := by
        dsimp only [qt]; rw [polyQuotAt_length]; omega
      have hQtNz : allZeroCoeffs qt = false := by
        cases hq : allZeroCoeffs qt with
        | false => rfl
        | true =>
          have hIns := polyInsertAt_allZero z0 qt hq (RoundPoly.evalCoeffs p z0) hRoot0
          rw [polyInsertAt_quot z0 p hpNe] at hIns
          rw [hIns] at hNz; cases hNz
      have ih := nonzero_poly_seed_roots_le N d qt hQtLen hQtNz
      have hPt : ∀ c : Fin N,
          (if RoundPoly.evalCoeffs p (decodeQuintic400 c.1) = CommRingOps.zero then 1 else 0) ≤
          (if decodeQuintic400 c.1 = z0 then 1 else 0) +
          (if RoundPoly.evalCoeffs qt (decodeQuintic400 c.1) = CommRingOps.zero then 1 else 0) := by
        intro c
        if hEv : RoundPoly.evalCoeffs p (decodeQuintic400 c.1) = CommRingOps.zero then
          have hDec := evalCoeffs_decomp_at z0 (decodeQuintic400 c.1) p
          rw [hEv, hRoot0, LawfulCommRing.zero_add] at hDec
          rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hDec.symm with hSub | hQ0
          · have hEqZ : decodeQuintic400 c.1 = z0 := LawfulCommRing.sub_eq_zero_iff.mp hSub
            rw [ite_eq_left hEv, ite_eq_left hEqZ]
            exact Nat.le_add_right 1 _
          · rw [ite_eq_left hEv, ite_eq_left hQ0]
            exact Nat.le_add_left 1 _
        else
          rw [ite_eq_right hEv]
          exact Nat.zero_le _
      have hSum := Nat.le_trans (qsum_le_qsum hPt) (Nat.le_of_eq (qsum_add _ _))
      have hPre := decodeQuintic400_preimage_le N z0
      rw [Nat.succ_mul, Nat.add_comm (d * _)]
      exact Nat.le_trans hSum (Nat.add_le_add hPre ih)

private def polySub : List QuinticGoldilocks → List QuinticGoldilocks → List QuinticGoldilocks
  | [], [] => []
  | a :: as, [] => a :: as
  | [], b :: bs => CommRingOps.neg b :: polySub [] bs
  | a :: as, b :: bs => (a -ᵍ b) :: polySub as bs

private theorem polySub_length_le :
    ∀ (p q : List QuinticGoldilocks) (m : Nat),
      p.length ≤ m → q.length ≤ m → (polySub p q).length ≤ m
  | [], [], _, _, _ => Nat.zero_le _
  | _ :: _, [], _, hp, _ => hp
  | [], _ :: _, 0, _, hq => nomatch hq
  | [], _ :: bs, m + 1, _, hq =>
    Nat.succ_le_succ (polySub_length_le [] bs m (Nat.zero_le _) (Nat.le_of_succ_le_succ hq))
  | _ :: _, _ :: _, 0, hp, _ => nomatch hp
  | _ :: as, _ :: bs, m + 1, hp, hq =>
    Nat.succ_le_succ (polySub_length_le as bs m (Nat.le_of_succ_le_succ hp) (Nat.le_of_succ_le_succ hq))

private theorem evalCoeffs_polySub (x : QuinticGoldilocks) :
    ∀ p q : List QuinticGoldilocks,
      RoundPoly.evalCoeffs (polySub p q) x =
        RoundPoly.evalCoeffs p x -ᵍ RoundPoly.evalCoeffs q x
  | [], [] => by simp only [polySub, RoundPoly.evalCoeffs]; constructive_ring
  | _ :: _, [] => by simp only [polySub, RoundPoly.evalCoeffs_nil]; constructive_ring
  | [], _ :: bs => by
    have ih := evalCoeffs_polySub x [] bs
    simp only [polySub, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil] at ih ⊢
    rw [ih]; constructive_ring
  | _ :: as, _ :: bs => by
    have ih := evalCoeffs_polySub x as bs
    simp only [polySub, RoundPoly.evalCoeffs_cons] at ih ⊢
    rw [ih]; constructive_ring

private theorem allZeroCoeffs_coeffAt :
    ∀ (r : List QuinticGoldilocks), allZeroCoeffs r = true →
      ∀ k : Nat, Qsag.coeffAt r k = CommRingOps.zero
  | [], _, k => Qsag.coeffAt_nil k
  | c :: _, h, 0 => by
    rw [allZeroCoeffs, Bool.and_eq_true] at h
    exact of_decide_eq_true h.1
  | _ :: cs, h, k + 1 => by
    rw [allZeroCoeffs, Bool.and_eq_true] at h
    exact allZeroCoeffs_coeffAt cs h.2 k

private theorem coeffAt_polySub :
    ∀ (p q : List QuinticGoldilocks) (k : Nat),
      Qsag.coeffAt (polySub p q) k = Qsag.coeffAt p k -ᵍ Qsag.coeffAt q k
  | [], [], k => by simp only [polySub, Qsag.coeffAt_nil]; constructive_ring
  | _ :: _, [], 0 => by
    simp only [polySub, Qsag.coeffAt_cons_zero, Qsag.coeffAt_nil]; constructive_ring
  | _ :: _, [], k + 1 => by
    simp only [polySub, Qsag.coeffAt_cons_succ, Qsag.coeffAt_nil]; constructive_ring
  | [], _ :: _, 0 => by
    simp only [polySub, Qsag.coeffAt_cons_zero, Qsag.coeffAt_nil]; constructive_ring
  | [], _ :: bs, k + 1 => by
    simp only [polySub, Qsag.coeffAt_cons_succ]
    rw [coeffAt_polySub [] bs k, Qsag.coeffAt_nil, Qsag.coeffAt_nil]
  | _ :: _, _ :: _, 0 => by
    simp only [polySub, Qsag.coeffAt_cons_zero]
  | _ :: as, _ :: bs, k + 1 => by
    simp only [polySub, Qsag.coeffAt_cons_succ]
    exact coeffAt_polySub as bs k

/-- Boolean detector: true iff two distinct polynomials in `cands` collide at `z`. -/
def gsListHasOodCollision : List (GsUniPoly QuinticGoldilocks) → QuinticGoldilocks → Bool
  | [], _ => false
  | P :: rest, z =>
    rest.any (fun Q => decide (RoundPoly.evalCoeffs P.coeffs z = RoundPoly.evalCoeffs Q.coeffs z)) ||
      gsListHasOodCollision rest z

private theorem ite_or_le_add (u v : Bool) :
    (if (u || v) = true then 1 else 0) ≤
      (if u = true then 1 else 0) + (if v = true then 1 else 0) := by
  cases u <;> cases v <;> decide

private theorem any_pair_seed_roots_le (N d : Nat) (P : GsUniPoly QuinticGoldilocks)
    (hP : P.coeffs.length ≤ d + 1) :
    ∀ (rest : List (GsUniPoly QuinticGoldilocks)),
      P ∉ rest → (∀ Q ∈ rest, Q.coeffs.length ≤ d + 1) →
      qsum N (fun c =>
        if rest.any (fun Q => decide (RoundPoly.evalCoeffs P.coeffs (decodeQuintic400 c.1) =
            RoundPoly.evalCoeffs Q.coeffs (decodeQuintic400 c.1))) = true then 1 else 0) ≤
        rest.length * (d * (N / quinticGoldilocksCard + 1))
  | [], _, _ => by
    have hZ : ∀ c : Fin N,
        (if ([] : List (GsUniPoly QuinticGoldilocks)).any
          (fun Q => decide (RoundPoly.evalCoeffs P.coeffs (decodeQuintic400 c.1) =
            RoundPoly.evalCoeffs Q.coeffs (decodeQuintic400 c.1))) = true then 1 else 0) = 0 :=
      fun _ => rfl
    rw [qsum_congr hZ, qsum_const, Nat.mul_zero]; exact Nat.zero_le _
  | Q :: qs, hNotMem, hDeg => by
    have hPNeQ : P ≠ Q := fun he => hNotMem (he ▸ List.mem_cons_self)
    have hPNotQs : P ∉ qs := fun hm => hNotMem (List.mem_cons_of_mem _ hm)
    have hQDeg : Q.coeffs.length ≤ d + 1 := hDeg Q List.mem_cons_self
    have hSubLen : (polySub P.coeffs Q.coeffs).length ≤ d + 1 :=
      polySub_length_le P.coeffs Q.coeffs (d + 1) hP hQDeg
    have hSubNz : allZeroCoeffs (polySub P.coeffs Q.coeffs) = false := by
      cases hz : allZeroCoeffs (polySub P.coeffs Q.coeffs) with
      | false => rfl
      | true =>
        exfalso; apply hPNeQ
        apply UPoly.ext_coeffAt; intro k
        have hk := allZeroCoeffs_coeffAt _ hz k
        rw [coeffAt_polySub] at hk
        exact LawfulCommRing.sub_eq_zero_iff.mp hk
    have hHead := nonzero_poly_seed_roots_le N d (polySub P.coeffs Q.coeffs) hSubLen hSubNz
    have ih := any_pair_seed_roots_le N d P hP qs hPNotQs
      (fun R hR => hDeg R (List.mem_cons_of_mem _ hR))
    have hPt : ∀ c : Fin N,
        (if (Q :: qs).any (fun R => decide (RoundPoly.evalCoeffs P.coeffs (decodeQuintic400 c.1) =
            RoundPoly.evalCoeffs R.coeffs (decodeQuintic400 c.1))) = true then 1 else 0) ≤
        (if RoundPoly.evalCoeffs (polySub P.coeffs Q.coeffs) (decodeQuintic400 c.1) =
            CommRingOps.zero then 1 else 0) +
        (if qs.any (fun R => decide (RoundPoly.evalCoeffs P.coeffs (decodeQuintic400 c.1) =
            RoundPoly.evalCoeffs R.coeffs (decodeQuintic400 c.1))) = true then 1 else 0) := by
      intro c
      have h1 := ite_or_le_add
        (decide (RoundPoly.evalCoeffs P.coeffs (decodeQuintic400 c.1) =
          RoundPoly.evalCoeffs Q.coeffs (decodeQuintic400 c.1)))
        (qs.any (fun R => decide (RoundPoly.evalCoeffs P.coeffs (decodeQuintic400 c.1) =
          RoundPoly.evalCoeffs R.coeffs (decodeQuintic400 c.1))))
      have h2 : (if decide (RoundPoly.evalCoeffs P.coeffs (decodeQuintic400 c.1) =
            RoundPoly.evalCoeffs Q.coeffs (decodeQuintic400 c.1)) = true then 1 else 0) =
          (if RoundPoly.evalCoeffs (polySub P.coeffs Q.coeffs) (decodeQuintic400 c.1) =
            CommRingOps.zero then 1 else 0) := by
        if hEq : RoundPoly.evalCoeffs P.coeffs (decodeQuintic400 c.1) =
            RoundPoly.evalCoeffs Q.coeffs (decodeQuintic400 c.1) then
          have hZ0 : RoundPoly.evalCoeffs (polySub P.coeffs Q.coeffs) (decodeQuintic400 c.1) =
              CommRingOps.zero := by
            rw [evalCoeffs_polySub, hEq, LawfulCommRing.sub_self]
          simp [hEq, hZ0]
        else
          have hNz0 : RoundPoly.evalCoeffs (polySub P.coeffs Q.coeffs) (decodeQuintic400 c.1) ≠
              CommRingOps.zero := fun hz0 => by
            rw [evalCoeffs_polySub] at hz0
            exact hEq (LawfulCommRing.sub_eq_zero_iff.mp hz0)
          simp [hEq, hNz0]
      rw [← h2]; exact h1
    have hSum := Nat.le_trans (qsum_le_qsum hPt) (Nat.le_of_eq (qsum_add _ _))
    simp only [List.length_cons, Nat.succ_mul, Nat.add_comm (qs.length * _)]
    exact Nat.le_trans hSum (Nat.add_le_add hHead ih)

private theorem binom2_succ_eq (m : Nat) : binom2 (m + 1) = m + binom2 m := by
  cases m with
  | zero => rw [binom2_eq, binom2_eq]
  | succ k =>
    rw [binom2_eq, binom2_eq]
    have hSub : k + 1 + 1 - 1 = k + 1 := rfl
    have hSub0 : k + 1 - 1 = k := rfl
    rw [hSub, hSub0]
    have h : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by
      rw [Nat.add_mul, Nat.mul_add]; omega
    rw [h, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.add_comm]

private theorem binom2_mono {a b : Nat} (h : a ≤ b) : binom2 a ≤ binom2 b := by
  rw [binom2_eq, binom2_eq]
  exact Nat.div_le_div_right (Nat.mul_le_mul h (Nat.sub_le_sub_right h 1))

private theorem prod_rearr_gs (K A B d : Nat) :
    A * (d * K) + K * B * d = K * (A + B) * d := by
  calc A * (d * K) + K * B * d
      = K * A * d + K * B * d := by
          congr 1
          calc A * (d * K) = A * (K * d) := by rw [Nat.mul_comm d K]
            _ = K * A * d := by rw [← Nat.mul_assoc, Nat.mul_comm A K]
    _ = (K * A + K * B) * d := (Nat.add_mul _ _ _).symm
    _ = K * (A + B) * d := by rw [← Nat.mul_add]


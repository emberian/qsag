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

#export_eqns encodeQuinticNat decodeQuintic400

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

theorem gsList_single_ood_bad_seeds_le (N d : Nat) :
    ∀ (cands : List (GsUniPoly QuinticGoldilocks)),
      cands.Nodup → (∀ P ∈ cands, P.coeffs.length ≤ d + 1) →
      qsum N (fun c => if gsListHasOodCollision cands (decodeQuintic400 c.1) = true then 1 else 0) ≤
        (N / quinticGoldilocksCard + 1) * binom2 cands.length * d
  | [], _, _ => by
    have hZ : ∀ c : Fin N,
        (if gsListHasOodCollision [] (decodeQuintic400 c.1) = true then 1 else 0) = 0 :=
      fun _ => rfl
    rw [qsum_congr hZ, qsum_const, Nat.mul_zero]; exact Nat.zero_le _
  | P :: rest, hNd, hDeg => by
    obtain ⟨hNotMem, hNdRest⟩ := List.nodup_cons.mp hNd
    have hHead := any_pair_seed_roots_le N d P (hDeg P List.mem_cons_self) rest hNotMem
      (fun Q hQ => hDeg Q (List.mem_cons_of_mem _ hQ))
    have ih := gsList_single_ood_bad_seeds_le N d rest hNdRest
      (fun Q hQ => hDeg Q (List.mem_cons_of_mem _ hQ))
    have hPt : ∀ c : Fin N,
        (if gsListHasOodCollision (P :: rest) (decodeQuintic400 c.1) = true then 1 else 0) ≤
        (if rest.any (fun Q => decide (RoundPoly.evalCoeffs P.coeffs (decodeQuintic400 c.1) =
            RoundPoly.evalCoeffs Q.coeffs (decodeQuintic400 c.1))) = true then 1 else 0) +
        (if gsListHasOodCollision rest (decodeQuintic400 c.1) = true then 1 else 0) :=
      fun _ => ite_or_le_add _ _
    have hSum := Nat.le_trans (qsum_le_qsum hPt) (Nat.le_of_eq (qsum_add _ _))
    have hComb := Nat.le_trans hSum (Nat.add_le_add hHead ih)
    simp only [List.length_cons, binom2_succ_eq]
    rwa [prod_rearr_gs (N / quinticGoldilocksCard + 1) rest.length (binom2 rest.length) d] at hComb

/-! ## §4. All 13 Deployed Schedules (`16 ≤ logCells ≤ 28`): Packed-Fiber Depth, `< 2^{-277}` OOD & `< 2^{-128}` QROM -/

/-- Explicit stage table matching `zkHemV2ProdStages` (`16 ≤ logCells ≤ 28`) with `@[expose]` transparency. -/
@[expose] def packedProdStages : Nat → List WhirStage
  | 16 => [⟨4, 14, 2, 5, 267, 4097, 8203, 1, 2048, 2048, 16, 23519292652270⟩, ⟨3, 13, 4, 2, 136, 514, 2069, 1, 512, 1023, 3, 9210⟩, ⟨3, 12, 6, 2, 92, 66, 525, 1, 1024, 4034, 3, 36309⟩]
  | 17 => [⟨5, 14, 2, 5, 267, 4097, 8203, 1, 2048, 2048, 17, 23519292652270⟩, ⟨3, 13, 4, 2, 136, 514, 2069, 1, 512, 1023, 3, 9210⟩, ⟨4, 11, 6, 2, 92, 34, 266, 1, 1024, 3974, 3, 47692⟩]
  | 18 => [⟨5, 15, 2, 5, 267, 8193, 16403, 1, 2048, 2048, 18, 47044326618137⟩, ⟨3, 14, 4, 2, 136, 1026, 4133, 1, 512, 1024, 3, 9219⟩, ⟨4, 12, 6, 2, 92, 66, 525, 1, 1024, 4034, 3, 48412⟩]
  | 19 => [⟨5, 16, 2, 5, 267, 16385, 32803, 1, 2048, 2048, 19, 94094395601011⟩, ⟨3, 15, 4, 2, 136, 2050, 8261, 1, 512, 1024, 3, 9219⟩, ⟨4, 13, 6, 2, 92, 130, 1041, 1, 1024, 4065, 3, 48784⟩]
  | 20 => [⟨5, 17, 2, 5, 267, 32769, 65603, 1, 2048, 2048, 20, 188194534092434⟩, ⟨3, 16, 4, 2, 136, 4098, 16517, 1, 512, 1024, 3, 9219⟩, ⟨4, 14, 6, 2, 92, 258, 2073, 1, 1024, 4081, 3, 48976⟩]
  | 21 => [⟨6, 17, 2, 5, 267, 32769, 65603, 1, 2048, 2048, 21, 188194534092434⟩, ⟨3, 16, 4, 2, 136, 4098, 16517, 1, 512, 1024, 3, 9219⟩, ⟨4, 14, 6, 2, 92, 258, 2073, 1, 1024, 4081, 3, 48976⟩]
  | 22 => [⟨6, 18, 2, 5, 267, 65537, 131203, 1, 2048, 2048, 22, 376394811338141⟩, ⟨4, 16, 4, 2, 136, 4098, 16517, 1, 512, 1024, 3, 12292⟩, ⟨4, 14, 6, 2, 92, 258, 2073, 1, 1024, 4081, 3, 48976⟩]
  | 23 => [⟨6, 19, 2, 5, 267, 131073, 262403, 1, 2048, 2048, 23, 752795365960994⟩, ⟨4, 17, 4, 2, 136, 8194, 33029, 1, 512, 1024, 3, 12292⟩, ⟨3, 16, 6, 2, 92, 1026, 8265, 1, 1024, 4093, 3, 36840⟩, ⟨3, 15, 8, 2, 70, 130, 2081, 1, 2048, 16258, 3, 146325⟩]
  | 24 => [⟨6, 20, 2, 5, 266, 262145, 524803, 1, 2048, 2048, 24, 1505596475272420⟩, ⟨4, 18, 4, 2, 136, 16386, 66053, 1, 512, 1024, 3, 12292⟩, ⟨3, 17, 6, 2, 92, 2050, 16521, 1, 1024, 4095, 3, 36858⟩, ⟨3, 16, 8, 2, 70, 258, 4145, 1, 2048, 16321, 3, 146892⟩]
  | 25 => [⟨6, 21, 2, 5, 266, 524289, 1049603, 1, 2048, 2048, 25, 3011198693928133⟩, ⟨4, 19, 4, 2, 136, 32770, 132101, 1, 512, 1024, 3, 12292⟩, ⟨4, 17, 6, 2, 92, 2050, 16521, 1, 1024, 4095, 3, 49144⟩, ⟨3, 16, 8, 2, 70, 258, 4145, 1, 2048, 16321, 3, 146892⟩]
  | 26 => [⟨6, 22, 2, 5, 266, 1048577, 2099203, 1, 2048, 2048, 26, 6022403131255990⟩, ⟨5, 19, 4, 2, 136, 32770, 132101, 1, 512, 1024, 3, 15365⟩, ⟨4, 17, 6, 2, 92, 2050, 16521, 1, 1024, 4095, 3, 49144⟩, ⟨3, 16, 8, 2, 70, 258, 4145, 1, 2048, 16321, 3, 146892⟩]
  | 27 => [⟨6, 23, 2, 5, 266, 2097153, 4198403, 1, 2048, 2048, 27, 12044812005919918⟩, ⟨5, 20, 4, 2, 136, 65538, 264197, 1, 512, 1024, 3, 15365⟩, ⟨4, 18, 6, 2, 92, 4098, 33033, 1, 1024, 4096, 3, 49156⟩, ⟨4, 16, 8, 2, 70, 258, 4145, 1, 2048, 16321, 3, 195856⟩]
  | 28 => [⟨6, 24, 2, 5, 266, 4194305, 8396803, 1, 2048, 2048, 28, 24089629755251882⟩, ⟨6, 20, 4, 2, 136, 65538, 264197, 1, 512, 1024, 3, 18438⟩, ⟨4, 18, 6, 2, 92, 4098, 33033, 1, 1024, 4096, 3, 49156⟩, ⟨4, 16, 8, 2, 70, 258, 4145, 1, 2048, 16321, 3, 195856⟩]
  | _ => []

@[expose] def packedProdSched (logCells : Nat) : WhirVerifierSchedule :=
  ⟨logCells, quinticGoldilocksCard, quinticGoldilocksCard_pos, packedProdStages logCells⟩

theorem packedProdSched_johnsonOk (logCells : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) :
    (packedProdSched logCells).johnsonOk = true := by
  have hc : logCells = 16 ∨ logCells = 17 ∨ logCells = 18 ∨ logCells = 19 ∨ logCells = 20 ∨
      logCells = 21 ∨ logCells = 22 ∨ logCells = 23 ∨ logCells = 24 ∨ logCells = 25 ∨
      logCells = 26 ∨ logCells = 27 ∨ logCells = 28 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

/-- Packed-fiber Merkle tree depth `st.logDomain` (one leaf per `2^{st.foldK}`-element fiber). -/
@[expose] def packedStageDepth (stages : List WhirStage) (i : Nat) : Nat :=
  match stages[i]? with
  | some st => st.logDomain
  | none => 0

/-- Scalar-leaf Merkle tree depth `st.logDomain + st.foldK` (matching `ClosedWhir.stageDepth`). -/
@[expose] def scalarStageDepth (stages : List WhirStage) (i : Nat) : Nat :=
  match stages[i]? with
  | some st => st.logDomain + st.foldK
  | none => 0

/-- Single-opening Merkle path verifier checking path length `depth q.1` and `merklePathRoot`. -/
@[expose] def checkMerkleOpening {D : Type} [DecidableEq D]
    (node : Nat → Nat → D → D → D) (depth : Nat → Nat) (roots : Nat → D)
    (q : Nat × Nat) (op : D × List D) : Bool :=
  decide (q.2 < 2 ^ depth q.1) && decide (op.2.length = depth q.1) &&
    decide (merklePathRoot node 0 q.2 op.1 op.2 = roots q.1)

private theorem prodStages_geom_ok (logCells : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) :
    ((packedProdSched logCells).stages.all fun st =>
      decide (0 < st.foldK ∧ st.logDomain + st.foldK ≤ 32 ∧ 2 ≤ st.listSize)) = true := by
  have hc : logCells = 16 ∨ logCells = 17 ∨ logCells = 18 ∨ logCells = 19 ∨ logCells = 20 ∨
      logCells = 21 ∨ logCells = 22 ∨ logCells = 23 ∨ logCells = 24 ∨ logCells = 25 ∨
      logCells = 26 ∨ logCells = 27 ∨ logCells = 28 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

/-- Honest `logDomain`-length packed-fiber authentication paths pass `checkMerkleOpening` under `packedStageDepth`. -/
theorem packed_stage_accepts_logDomain_path {D : Type} [DecidableEq D]
    (logCells : Nat) (i : Nat) (st : WhirStage)
    (hst : (packedProdSched logCells).stages[i]? = some st)
    (node : Nat → Nat → D → D → D) (leafDigests : Nat → Nat → D)
    (j : Nat) (hj : j < st.domainSize) :
    let depth := packedStageDepth (packedProdSched logCells).stages
    let leafD := treeNode node (leafDigests i) 0 j
    let path := treePathFrom node (leafDigests i) 0 j st.logDomain
    checkMerkleOpening node depth (fun k => treeNode node (leafDigests k) (depth k) 0)
      (i, j) (leafD, path) = true := by
  dsimp only
  have hDepth : packedStageDepth (packedProdSched logCells).stages i = st.logDomain := by
    simp [packedStageDepth, hst]
  unfold checkMerkleOpening
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨decide_eq_true (by rw [hDepth]; exact hj),
           decide_eq_true (by rw [hDepth]; exact treePathFrom_length ..)⟩,
         decide_eq_true ?_⟩
  rw [hDepth]
  have h := treePathFrom_opens node (leafDigests i) st.logDomain 0 j
  rw [Nat.zero_add, Nat.div_eq_of_lt (show j < 2 ^ st.logDomain from hj)] at h
  exact h

/-- `#tooth` Scalar `scalarStageDepth` (`logDomain + foldK`) rejects every `logDomain`-length packed-fiber path. -/
theorem tooth_scalar_stage_rejects_logDomain_path {D : Type} [DecidableEq D]
    (logCells : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28)
    (i : Nat) (st : WhirStage)
    (hst : (packedProdSched logCells).stages[i]? = some st)
    (node : Nat → Nat → D → D → D) (roots : Nat → D)
    (j : Nat) (leafD : D) (path : List D) (hLen : path.length = st.logDomain) :
    checkMerkleOpening node (scalarStageDepth (packedProdSched logCells).stages)
      roots (i, j) (leafD, path) = false := by
  have hs := List.mem_of_getElem? hst
  have hg := of_decide_eq_true (List.all_eq_true.mp (prodStages_geom_ok logCells hLo hHi) st hs)
  have hDepth : scalarStageDepth (packedProdSched logCells).stages i = st.logDomain + st.foldK := by
    simp [scalarStageDepth, hst]
  have hNe : path.length ≠ st.logDomain + st.foldK := by omega
  unfold checkMerkleOpening
  dsimp only
  rw [hDepth, decide_eq_false hNe, Bool.and_false, Bool.false_and]

/-- Realizable single-OOD 400-bit seed bound (`≥ 1` seed, `< 2^{-277}`). -/
@[expose] def singleOodSeedBound (s : WhirStage) : RatBound :=
  ⟨(2 ^ 400 / quinticGoldilocksCard + 1) * binom2 s.listSize * s.degBound,
   2 ^ 400, Nat.two_pow_pos 400⟩

/-- Packed-fiber per-stage round bounds replacing `< 2^{-400}` OOD with `singleOodSeedBound` (`< 2^{-277}`). -/
def packedStageRoundBounds (q : Nat) (hq : 0 < q) (s : WhirStage) : List RatBound :=
  List.replicate s.foldK (s.foldBound q hq) ++ [singleOodSeedBound s, s.shiftBound q hq]

def packedStagesRoundBounds (q : Nat) (hq : 0 < q) : List WhirStage → List RatBound
  | [] => []
  | s :: rest => packedStageRoundBounds q hq s ++ packedStagesRoundBounds q hq rest

theorem packedStagesRoundBounds_length (q : Nat) (hq : 0 < q) :
    ∀ stages : List WhirStage, (packedStagesRoundBounds q hq stages).length = roundsOf stages
  | [] => rfl
  | s :: rest => by
    simp only [packedStagesRoundBounds, packedStageRoundBounds, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil, packedStagesRoundBounds_length q hq rest,
      roundsOf, stageRounds]

def packedProdQromError (logCells Q : Nat) : RatBound :=
  RatBound.sumList
    ((packedStagesRoundBounds quinticGoldilocksCard quinticGoldilocksCard_pos
      (packedProdStages logCells)).map (dfmRoundScale Q))

theorem deployed_single_ood_gs_bad_lt_277
    (logCells : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28)
    (st : WhirStage) (hst : st ∈ (packedProdSched logCells).stages)
    (shift : QuinticGoldilocks) (hnz : shift ≠ CommRingOps.zero)
    (word : QuinticGoldilocks → QuinticGoldilocks) :
    let dom := ZkHemV2.fiberRoots st.logDomain shift
    let cands := gsDecodeList st.degBound st.agree dom word
    1 ≤ (singleOodSeedBound st).num ∧
    cands.length ≤ st.listSize ∧
    qsum (2 ^ 400) (fun c =>
      if gsListHasOodCollision cands (decodeQuintic400 c.1) = true then 1 else 0) ≤
      (singleOodSeedBound st).num ∧
    RatBound.lt (singleOodSeedBound st) (RatBound.invPow2 277) := by
  intro dom cands
  have hg := of_decide_eq_true (List.all_eq_true.mp (prodStages_geom_ok logCells hLo hHi) st hst)
  have hj := List.all_eq_true.mp (packedProdSched_johnsonOk logCells hLo hHi) st hst
  have hDomNd := ZkHemV2.fiberRoots_nodup st.logDomain (by omega) hnz
  have hDomLen : dom.length = st.domainSize := ZkHemV2.fiberRoots_length _ _
  have hListLe : cands.length ≤ st.listSize :=
    st.decode_list_le hj dom word hDomNd hDomLen
  have hdA : st.degBound + 1 ≤ st.agree := by
    obtain ⟨hnd, _⟩ := st.johnson_list_le hj
    unfold WhirStage.johnsonOk at hj
    obtain ⟨_, _, hAn, _⟩ := of_decide_eq_true hj
    apply Nat.lt_of_not_ge; intro hge
    exact Nat.not_le_of_gt hnd (Nat.mul_le_mul hAn hge)
  have hSeeds := gsList_single_ood_bad_seeds_le (2 ^ 400) st.degBound cands
    (gsDecodeList_nodup st.degBound st.agree dom word)
    (fun P hP => ((mem_gsDecodeList_iff word hDomNd hdA P).mp hP).1)
  have hSeedsCap :
      (2 ^ 400 / quinticGoldilocksCard + 1) * binom2 cands.length * st.degBound ≤
      (singleOodSeedBound st).num :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (binom2_mono hListLe))
  have hCheck277 :
      ((packedProdSched logCells).stages.all fun s =>
        decide (1 ≤ (2 ^ 400 / quinticGoldilocksCard + 1) * (s.listSize * (s.listSize - 1) / 2) * s.degBound ∧
          (2 ^ 400 / quinticGoldilocksCard + 1) * (s.listSize * (s.listSize - 1) / 2) * s.degBound * 2 ^ 277 <
            1 * 2 ^ 400)) = true := by
    have hc : logCells = 16 ∨ logCells = 17 ∨ logCells = 18 ∨ logCells = 19 ∨ logCells = 20 ∨
        logCells = 21 ∨ logCells = 22 ∨ logCells = 23 ∨ logCells = 24 ∨ logCells = 25 ∨
        logCells = 26 ∨ logCells = 27 ∨ logCells = 28 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  obtain ⟨hPos1, hLt277⟩ := of_decide_eq_true (List.all_eq_true.mp hCheck277 st hst)
  have hPos' : 1 ≤ (singleOodSeedBound st).num := by
    unfold singleOodSeedBound; dsimp only; rwa [binom2_eq]
  have hLt' : RatBound.lt (singleOodSeedBound st) (RatBound.invPow2 277) := by
    show (singleOodSeedBound st).num * 2 ^ 277 < 1 * 2 ^ 400
    unfold singleOodSeedBound; dsimp only; rwa [binom2_eq]
  exact ⟨hPos', hListLe, Nat.le_trans hSeeds hSeedsCap, hLt'⟩

private inductive RBoundsLeP : List RatBound → List RatBound → Prop where
  | nil : RBoundsLeP [] []
  | cons {x y xs ys} : RatBound.le x y → RBoundsLeP xs ys → RBoundsLeP (x :: xs) (y :: ys)

private theorem RBoundsLeP.append {xs ys us vs : List RatBound}
    (h : RBoundsLeP xs ys) (k : RBoundsLeP us vs) : RBoundsLeP (xs ++ us) (ys ++ vs) := by
  induction h with | nil => exact k | cons hxy _ ih => exact .cons hxy ih

private theorem scaled_sum_mono_packed (Q : Nat) {xs ys : List RatBound} (h : RBoundsLeP xs ys) :
    RatBound.le (RatBound.sumList (xs.map (dfmRoundScale Q)))
      (RatBound.sumList (ys.map (dfmRoundScale Q))) := by
  induction h with
  | nil => exact RatBound.le_refl _
  | @cons x y _ _ hxy _ ih =>
    exact RatBound.add_le_add
      (by show (2 * Q + 1) ^ 2 * x.num * y.den ≤ (2 * Q + 1) ^ 2 * y.num * x.den
          simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left ((2 * Q + 1) ^ 2) hxy) ih

private theorem dfmRoundScale_mono {Q Q' : Nat} (h : Q ≤ Q') (b : RatBound) :
    RatBound.le (dfmRoundScale Q b) (dfmRoundScale Q' b) := by
  show (2 * Q + 1) ^ 2 * b.num * b.den ≤ (2 * Q' + 1) ^ 2 * b.num * b.den
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2))

private theorem sumList_map_dfm_mono {Q Q' : Nat} (h : Q ≤ Q') :
    ∀ bs : List RatBound,
      RatBound.le (RatBound.sumList (bs.map (dfmRoundScale Q)))
        (RatBound.sumList (bs.map (dfmRoundScale Q')))
  | [] => RatBound.le_refl _
  | b :: bs => RatBound.add_le_add (dfmRoundScale_mono h b) (sumList_map_dfm_mono h bs)

private def shiftCapNumP (qCount : Nat) : Nat :=
  if qCount = 267 then 2052 else if qCount = 266 then 2051 else if qCount = 136 then 1036
  else if qCount = 92 then 540 else 261

private theorem shiftCapNumP_pow_ok {t : Nat} (ht : t = 267 ∨ t = 266 ∨ t = 136 ∨ t = 92 ∨ t = 70) :
    (shiftCapNumP t) ^ t * 2 ^ 267 ≤ 3 * 4096 ^ t := by
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private def checkPackedStage265 (q : Nat) (s : WhirStage) : Bool :=
  decide ((s.listSize * s.sumcheckDeg + s.mcaNum) * 2 ^ 265 ≤ q ∧
    (2 ^ 400 / quinticGoldilocksCard + 1) * (s.listSize * (s.listSize - 1) / 2) * s.degBound * 2 ^ 265 ≤ 2 ^ 400 ∧
    (s.queryCount = 267 ∨ s.queryCount = 266 ∨ s.queryCount = 136 ∨ s.queryCount = 92 ∨ s.queryCount = 70) ∧
    (s.agree + s.foldK) * 4096 ≤ shiftCapNumP s.queryCount * s.domainSize ∧
    s.listSize * (s.queryCount + s.oodCount) * 2 ^ 267 ≤ q)

private theorem replicate_add_p {α : Type} (x : α) :
    ∀ (a b : Nat), List.replicate (a + b) x = List.replicate a x ++ List.replicate b x
  | 0, _ => by simp only [Nat.zero_add, List.replicate_zero, List.nil_append]
  | a + 1, b => by simp only [Nat.succ_add, List.replicate_succ, List.cons_append, replicate_add_p x a b]

private theorem packed_stage_covers_265 (q : Nat) (hq : 0 < q) (s : WhirStage)
    (hOk : checkPackedStage265 q s = true) :
    RBoundsLeP (packedStageRoundBounds q hq s)
      (List.replicate (stageRounds s) (RatBound.invPow2 265)) := by
  obtain ⟨hf, ho, hQt, hRatio, hComb⟩ := of_decide_eq_true hOk
  have hFold : RatBound.le (s.foldBound q hq) (RatBound.invPow2 265) := by
    rw [WhirStage.foldBound_eq]; show _ ≤ 1 * q; rw [Nat.one_mul]; exact hf
  have hOod : RatBound.le (singleOodSeedBound s) (RatBound.invPow2 265) := by
    show (singleOodSeedBound s).num * 2 ^ 265 ≤ 1 * 2 ^ 400
    unfold singleOodSeedBound; dsimp only; rw [binom2_eq, Nat.one_mul]; exact ho
  have hShift1 : RatBound.le ⟨(s.agree + s.foldK) ^ s.queryCount, s.domainSize ^ s.queryCount,
        Nat.pow_pos (Nat.two_pow_pos s.logDomain)⟩ ⟨3, 2 ^ 267, Nat.two_pow_pos 267⟩ := by
    show (s.agree + s.foldK) ^ s.queryCount * 2 ^ 267 ≤ 3 * s.domainSize ^ s.queryCount
    have hPow := Nat.pow_le_pow_left hRatio s.queryCount
    rw [Nat.mul_pow, Nat.mul_pow] at hPow
    have hMul : ((s.agree + s.foldK) ^ s.queryCount * 2 ^ 267) * 4096 ^ s.queryCount ≤
        (3 * s.domainSize ^ s.queryCount) * 4096 ^ s.queryCount := by
      calc ((s.agree + s.foldK) ^ s.queryCount * 2 ^ 267) * 4096 ^ s.queryCount
          = ((s.agree + s.foldK) ^ s.queryCount * 4096 ^ s.queryCount) * 2 ^ 267 := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ ((shiftCapNumP s.queryCount) ^ s.queryCount * s.domainSize ^ s.queryCount) * 2 ^ 267 :=
              Nat.mul_le_mul_right _ hPow
        _ = ((shiftCapNumP s.queryCount) ^ s.queryCount * 2 ^ 267) * s.domainSize ^ s.queryCount := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ (3 * 4096 ^ s.queryCount) * s.domainSize ^ s.queryCount :=
              Nat.mul_le_mul_right _ (shiftCapNumP_pow_ok hQt)
        _ = (3 * s.domainSize ^ s.queryCount) * 4096 ^ s.queryCount := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    exact nat_le_of_mul_le_mul_right' hMul (Nat.pow_pos (by decide : 0 < 4096))
  have hShift2 : RatBound.le ⟨s.listSize * (s.queryCount + s.oodCount), q, hq⟩
      ⟨1, 2 ^ 267, Nat.two_pow_pos 267⟩ := by
    show _ ≤ 1 * q; rw [Nat.one_mul]; exact hComb
  have h3Plus1 : RatBound.le
      (RatBound.add ⟨3, 2 ^ 267, Nat.two_pow_pos 267⟩ ⟨1, 2 ^ 267, Nat.two_pow_pos 267⟩)
      (RatBound.invPow2 265) := by decide +kernel
  have hShift : RatBound.le (s.shiftBound q hq) (RatBound.invPow2 265) := by
    rw [WhirStage.shiftBound_eq]; exact RatBound.le_trans (RatBound.add_le_add hShift1 hShift2) h3Plus1
  unfold packedStageRoundBounds stageRounds
  rw [replicate_add_p _ s.foldK 2]
  refine RBoundsLeP.append ?_ (.cons hOod (.cons hShift .nil))
  induction s.foldK with | zero => exact .nil | succ _ ih => exact .cons hFold ih

private theorem packed_stages_cover_265 (q : Nat) (hq : 0 < q) :
    ∀ stages : List WhirStage, stages.all (checkPackedStage265 q) = true →
      RBoundsLeP (packedStagesRoundBounds q hq stages)
        (List.replicate (roundsOf stages) (RatBound.invPow2 265))
  | [], _ => .nil
  | s :: rest, hAll => by
    rw [List.all_cons, Bool.and_eq_true] at hAll
    unfold packedStagesRoundBounds roundsOf
    rw [replicate_add_p _ (stageRounds s) (roundsOf rest)]
    exact RBoundsLeP.append (packed_stage_covers_265 q hq s hAll.1)
      (packed_stages_cover_265 q hq rest hAll.2)

private theorem sumList_replicate_le_scale_p (b : RatBound) :
    ∀ r : Nat, RatBound.le (RatBound.sumList (List.replicate r b)) ⟨r * b.num, b.den, b.h_pos⟩
  | 0 => by show 0 * b.den ≤ 0 * b.num * 1; simp
  | r + 1 => by
    have ih := sumList_replicate_le_scale_p b r
    let sr := RatBound.sumList (List.replicate r b)
    show (b.num * sr.den + sr.num * b.den) * b.den ≤ ((r + 1) * b.num) * (b.den * sr.den)
    calc (b.num * sr.den + sr.num * b.den) * b.den
        ≤ (b.num * sr.den + r * b.num * sr.den) * b.den :=
          Nat.mul_le_mul_right b.den (Nat.add_le_add_left ih _)
      _ = ((r + 1) * b.num) * (b.den * sr.den) := by
          rw [Nat.succ_mul, Nat.add_comm (r * b.num) b.num, Nat.add_mul, Nat.add_mul]
          have e1 : b.num * sr.den * b.den = b.num * (b.den * sr.den) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          have e2 : r * b.num * sr.den * b.den = r * b.num * (b.den * sr.den) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          rw [e1, e2]

theorem packedProdQromError_eq (n Q : Nat) : packedProdQromError n Q =
    RatBound.sumList ((packedStagesRoundBounds quinticGoldilocksCard quinticGoldilocksCard_pos
      (packedProdStages n)).map (dfmRoundScale Q)) := by unfold packedProdQromError; rfl

/-- The one-query, 16-log-cell budget covers two guesses from a 512-bit sample. -/
theorem packedProdQromError_16_covers_two_guesses :
    RatBound.le ⟨2, 2^512, Nat.two_pow_pos _⟩ (packedProdQromError 16 1) := by
  let st := (packedProdStages 16)[0]'(by decide)
  apply RatBound.le_trans (b := dfmRoundScale 1 (st.foldBound quinticGoldilocksCard quinticGoldilocksCard_pos))
  · rw [WhirStage.foldBound_eq]; decide +kernel
  · apply RatBound.le_add_left

/-- **All 13 Deployed Packed-Fiber Schedules (`16 ≤ logCells ≤ 28`) Clear `< 2^{-128}` at `Q ≤ 2^{64}`:**
    Replaces the `< 2^{-400}` OOD bound with the realizable `< 2^{-277}` `singleOodSeedBound` and supports
    both `.turboShake400` and `.poseidon2Gl24` commitment profiles. -/
theorem zkHemV2_packed_all13_qrom_lt_128_at_2pow64
    (prof : WhirCommitmentProfile) (logCells Q : Nat)
    (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) (hQ : Q ≤ 2 ^ 64) :
    RatBound.lt
      (RatBound.add (packedProdQromError logCells Q) (merkleProfileQromBound prof Q))
      (RatBound.invPow2 128) := by
  have hAll265 :
      (packedProdStages logCells).all (checkPackedStage265 quinticGoldilocksCard) = true ∧
      roundsOf (packedProdStages logCells) ≤ 28 := by
    have hc : logCells = 16 ∨ logCells = 17 ∨ logCells = 18 ∨ logCells = 19 ∨ logCells = 20 ∨
        logCells = 21 ∨ logCells = 22 ∨ logCells = 23 ∨ logCells = 24 ∨ logCells = 25 ∨
        logCells = 26 ∨ logCells = 27 ∨ logCells = 28 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact ⟨by decide +kernel, by decide +kernel⟩
  have hMonoQ : RatBound.le
      (RatBound.add (packedProdQromError logCells Q) (merkleProfileQromBound prof Q))
      (RatBound.add (packedProdQromError logCells (2 ^ 64)) (merkle400QromBound (2 ^ 64))) :=
    RatBound.add_le_add (sumList_map_dfm_mono hQ _)
      (RatBound.le_trans (merkleProfileQromBound_mono prof hQ) (merkleProfileQromBound_le_400 prof (2 ^ 64)))
  let b265 := dfmRoundScale (2 ^ 64) (RatBound.invPow2 265)
  have hCov := packed_stages_cover_265 quinticGoldilocksCard quinticGoldilocksCard_pos
    (packedProdStages logCells) hAll265.1
  have hEnv1 : RatBound.le (packedProdQromError logCells (2 ^ 64))
      (RatBound.sumList (List.replicate (roundsOf (packedProdStages logCells)) b265)) := by
    unfold packedProdQromError
    rw [← List.map_replicate]
    exact scaled_sum_mono_packed (2 ^ 64) hCov
  have hEnv2 := sumList_replicate_le_scale_p b265 (roundsOf (packedProdStages logCells))
  have hEnv3 : RatBound.le
      ⟨roundsOf (packedProdStages logCells) * b265.num, b265.den, b265.h_pos⟩
      ⟨28 * b265.num, b265.den, b265.h_pos⟩ := by
    show roundsOf (packedProdStages logCells) * b265.num * b265.den ≤ 28 * b265.num * b265.den
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hAll265.2)
  have hCap28 : RatBound.lt
      (RatBound.add ⟨28 * b265.num, b265.den, b265.h_pos⟩ (merkle400QromBound (2 ^ 64)))
      (RatBound.invPow2 128) := by
    dsimp only [b265]; decide +kernel
  exact ratBound_lt_of_le_of_lt_packed
    (RatBound.le_trans hMonoQ
      (RatBound.add_le_add (RatBound.le_trans hEnv1 (RatBound.le_trans hEnv2 hEnv3))
        (RatBound.le_refl _)))
    hCap28

/-! ## §5. `[DKT26]` Quintic `Fp5` Recursive Margin Schedule (`logCells = 20`, `d ≤ 16`, `Q ≤ 2^{64}`) -/

/-- Recursive `2^{20}`-row (`logCells = 20`) 3-stage `[DKT26]` margin schedule (`m = 24`, `q = (304, 148, 100)`),
    sizing every round below `2^{-285}` so `131,071` (`d = 16`) recursive nodes clear `< 2^{-128}` at `Q ≤ 2^{64}`. -/
@[expose] def zkHemV2RecursiveMarginStages : List WhirStage :=
  [⟨5, 17, 2, 5, 304, 32769, 66904, 1, 128, 128, 20, 20560025553⟩,
   ⟨3, 16, 4, 2, 148, 4098, 16517, 1, 512, 1024, 3, 9219⟩,
   ⟨4, 14, 6, 2, 100, 258, 2073, 1, 1024, 4081, 3, 48976⟩]

@[expose] def zkHemV2RecursiveMarginSched : WhirVerifierSchedule :=
  ⟨20, quinticGoldilocksCard, quinticGoldilocksCard_pos, zkHemV2RecursiveMarginStages⟩

theorem zkHemV2RecursiveMarginSched_johnson_and_dkt26 :
    zkHemV2RecursiveMarginSched.johnsonOk = true ∧
    (2 * 24 + 1) * (2 * 24 + 1) * (4 * 2 ^ 15) * (2 ^ 15 + 2) ≤ (2 * 24 * 66904) * (2 * 24 * 66904) := by
  exact ⟨by decide +kernel, by decide +kernel⟩

private def shiftCapRec (qCount : Nat) : Nat :=
  if qCount = 304 then 2092 else if qCount = 148 then 1036 else 540

private theorem shiftCapRec_pow_ok {t : Nat} (ht : t = 304 ∨ t = 148 ∨ t = 100) :
    (shiftCapRec t) ^ t * 2 ^ 286 ≤ 4096 ^ t := by
  rcases ht with rfl | rfl | rfl <;> decide +kernel

private theorem rec_stage_covers_285 (s : WhirStage)
    (hs : s ∈ zkHemV2RecursiveMarginStages) :
    RBoundsLeP (s.roundBounds quinticGoldilocksCard quinticGoldilocksCard_pos)
      (List.replicate (stageRounds s) (RatBound.invPow2 285)) := by
  have hChk : decide (
      (s.listSize * s.sumcheckDeg + s.mcaNum) * 2 ^ 285 ≤ quinticGoldilocksCard ∧
      (s.listSize * (s.listSize - 1) / 2) * s.degBound ^ s.oodCount * 2 ^ 285 ≤ quinticGoldilocksCard ^ s.oodCount ∧
      (s.queryCount = 304 ∨ s.queryCount = 148 ∨ s.queryCount = 100) ∧
      (s.agree + s.foldK) * 4096 ≤ shiftCapRec s.queryCount * s.domainSize ∧
      s.listSize * (s.queryCount + s.oodCount) * 2 ^ 286 ≤ quinticGoldilocksCard) = true := by
    simp only [zkHemV2RecursiveMarginStages, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide +kernel
  obtain ⟨hf, ho, hQt, hRatio, hComb⟩ := of_decide_eq_true hChk
  have hq := quinticGoldilocksCard_pos
  have hFold : RatBound.le (s.foldBound quinticGoldilocksCard hq) (RatBound.invPow2 285) := by
    rw [WhirStage.foldBound_eq]; show _ ≤ 1 * _; rw [Nat.one_mul]; exact hf
  have hOod : RatBound.le (s.oodBound quinticGoldilocksCard hq) (RatBound.invPow2 285) := by
    rw [WhirStage.oodBound_eq]; show binom2 _ * _ * _ ≤ 1 * _; rw [binom2_eq, Nat.one_mul]; exact ho
  have hShift1 : RatBound.le ⟨(s.agree + s.foldK) ^ s.queryCount, s.domainSize ^ s.queryCount,
        Nat.pow_pos (Nat.two_pow_pos s.logDomain)⟩ (RatBound.invPow2 286) := by
    show (s.agree + s.foldK) ^ s.queryCount * 2 ^ 286 ≤ 1 * s.domainSize ^ s.queryCount
    rw [Nat.one_mul]
    have hPow := Nat.pow_le_pow_left hRatio s.queryCount
    rw [Nat.mul_pow, Nat.mul_pow] at hPow
    have hMul : ((s.agree + s.foldK) ^ s.queryCount * 2 ^ 286) * 4096 ^ s.queryCount ≤
        s.domainSize ^ s.queryCount * 4096 ^ s.queryCount := by
      calc ((s.agree + s.foldK) ^ s.queryCount * 2 ^ 286) * 4096 ^ s.queryCount
          = ((s.agree + s.foldK) ^ s.queryCount * 4096 ^ s.queryCount) * 2 ^ 286 := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ ((shiftCapRec s.queryCount) ^ s.queryCount * s.domainSize ^ s.queryCount) * 2 ^ 286 :=
              Nat.mul_le_mul_right _ hPow
        _ = ((shiftCapRec s.queryCount) ^ s.queryCount * 2 ^ 286) * s.domainSize ^ s.queryCount := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ 4096 ^ s.queryCount * s.domainSize ^ s.queryCount :=
              Nat.mul_le_mul_right _ (shiftCapRec_pow_ok hQt)
        _ = s.domainSize ^ s.queryCount * 4096 ^ s.queryCount := Nat.mul_comm _ _
    exact nat_le_of_mul_le_mul_right' hMul (Nat.pow_pos (by decide : 0 < 4096))
  have hShift2 : RatBound.le ⟨s.listSize * (s.queryCount + s.oodCount), quinticGoldilocksCard, hq⟩
      (RatBound.invPow2 286) := by
    show _ ≤ 1 * _; rw [Nat.one_mul]; exact hComb
  have hHalf : RatBound.le (RatBound.add (RatBound.invPow2 286) (RatBound.invPow2 286))
      (RatBound.invPow2 285) := by decide +kernel
  have hShift : RatBound.le (s.shiftBound quinticGoldilocksCard hq) (RatBound.invPow2 285) := by
    rw [WhirStage.shiftBound_eq]; exact RatBound.le_trans (RatBound.add_le_add hShift1 hShift2) hHalf
  rw [WhirStage.roundBounds_eq]; unfold stageRounds; rw [replicate_add_p _ s.foldK 2]
  refine RBoundsLeP.append ?_ (.cons hOod (.cons hShift .nil))
  induction s.foldK with | zero => exact .nil | succ _ ih => exact .cons hFold ih

/-- **Deployment-Scale Recursive Margin Schedule `< 2^{-128}` Bound (`zkHemV2RecursiveMargin_tree_lt_128`):**
    For all tree depths `d ≤ 16` (`≤ 65,536` regional leaf shards, `≤ 131,071` tree nodes) and
    `Q ≤ 2^{64}` quantum oracle queries, `(2^{d+1} - 1) · ε_step + ε_qromColl(Q) < 2^{-128}`. -/
private theorem recMargin_covAll :
    RBoundsLeP
      (stagesRoundBounds quinticGoldilocksCard quinticGoldilocksCard_pos zkHemV2RecursiveMarginStages)
      (List.replicate 18 (RatBound.invPow2 285)) := by
  unfold zkHemV2RecursiveMarginStages
  rw [stagesRoundBounds_cons, stagesRoundBounds_cons, stagesRoundBounds_cons, stagesRoundBounds_nil,
      List.append_nil]
  have h18 : List.replicate 18 (RatBound.invPow2 285) =
      List.replicate 7 (RatBound.invPow2 285) ++
      (List.replicate 5 (RatBound.invPow2 285) ++ List.replicate 6 (RatBound.invPow2 285)) := rfl
  rw [h18]
  exact RBoundsLeP.append (rec_stage_covers_285 _ List.mem_cons_self)
    (RBoundsLeP.append (rec_stage_covers_285 _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (rec_stage_covers_285 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

private theorem recMargin_schedLe {Q : Nat} (hQ : Q ≤ 2 ^ 64) :
    let b285 := dfmRoundScale (2 ^ 64) (RatBound.invPow2 285)
    RatBound.le (scheduleQromError zkHemV2RecursiveMarginSched Q)
      ⟨18 * b285.num, b285.den, b285.h_pos⟩ := by
  intro b285
  refine RatBound.le_trans (scheduleQromError_mono zkHemV2RecursiveMarginSched hQ) ?_
  refine RatBound.le_trans ?_ (sumList_replicate_le_scale_p b285 18)
  rw [← List.map_replicate, scheduleQromError_eq, WhirVerifierSchedule.roundBounds_eq]
  exact scaled_sum_mono_packed (2 ^ 64) recMargin_covAll

private theorem recMargin_top :
    let b285 := dfmRoundScale (2 ^ 64) (RatBound.invPow2 285)
    RatBound.lt
      (RatBound.add ⟨131071 * (18 * b285.num), b285.den, b285.h_pos⟩ (merkle400QromBound (2 ^ 64)))
      (RatBound.invPow2 128) := by
  intro b285
  dsimp only [b285]; decide +kernel

private theorem ratBound_scale_le_of_le {n m k : Nat} (e b : RatBound)
    (hn : n ≤ m) (he : RatBound.le e ⟨k * b.num, b.den, b.h_pos⟩) :
    RatBound.le (RatBound.scale n e) ⟨m * (k * b.num), b.den, b.h_pos⟩ := by
  show n * e.num * b.den ≤ m * (k * b.num) * e.den
  calc n * e.num * b.den
      ≤ m * e.num * b.den := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hn)
    _ = m * (e.num * b.den) := Nat.mul_assoc _ _ _
    _ ≤ m * (k * b.num * e.den) := Nat.mul_le_mul_left _ he
    _ = m * (k * b.num) * e.den := (Nat.mul_assoc _ _ _).symm

private theorem pow2_17_sub1_le {d : Nat} (hd : d ≤ 16) : 2 ^ (d + 1) - 1 ≤ 131071 := by
  have h17 : 2 ^ 17 - 1 = 131071 := by decide +kernel
  rw [← h17]
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ hd)) 1

theorem zkHemV2RecursiveMargin_tree_lt_128
    (prof : WhirCommitmentProfile) {d Q : Nat} (hd : d ≤ 16) (hQ : Q ≤ 2 ^ 64) :
    RatBound.lt
      (RatBound.add
        (RatBound.scale (2 ^ (d + 1) - 1) (scheduleQromError zkHemV2RecursiveMarginSched Q))
        (merkleProfileQromBound prof Q))
      (RatBound.invPow2 128) :=
  ratBound_lt_of_le_of_lt_packed
    (RatBound.add_le_add
      (ratBound_scale_le_of_le (scheduleQromError zkHemV2RecursiveMarginSched Q)
        (dfmRoundScale (2 ^ 64) (RatBound.invPow2 285)) (pow2_17_sub1_le hd) (recMargin_schedLe hQ))
      (RatBound.le_trans (merkleProfileQromBound_mono prof hQ) (merkleProfileQromBound_le_400 prof (2 ^ 64))))
    recMargin_top

def unadjustedStage20 : WhirStage :=
  ⟨5, 17, 2, 5, 267, 32769, 65603, 1, 2048, 2048, 20, 188194534092434⟩

/-- `#tooth` Unadjusted single-proof Stage-0 fold budget (`packedProdSched 20`, `L_0 = 2048`, `mca0 = 188,194,534,092,434`)
    exceeds `2^{-128}` when summed across `131,071` (`d = 16`) recursive nodes at `Q = 2^{64}`,
    demonstrating why `zkHemV2RecursiveMarginSched` (`[DKT26]` `m = 24`, `q = (304, 148, 100)`) is necessary. -/
theorem tooth_unadjusted_single_sched_fails_d16 (prof : WhirCommitmentProfile) :
    ¬ RatBound.lt
        (RatBound.add
          (RatBound.scale 131071
            (dfmRoundScale (2 ^ 64)
              (unadjustedStage20.foldBound quinticGoldilocksCard quinticGoldilocksCard_pos)))
          (merkleProfileQromBound prof (2 ^ 64)))
        (RatBound.invPow2 128) := by
  intro hLt
  have hSub : RatBound.le
      (RatBound.scale 131071
        (dfmRoundScale (2 ^ 64)
          (unadjustedStage20.foldBound quinticGoldilocksCard quinticGoldilocksCard_pos)))
      (RatBound.add
        (RatBound.scale 131071
          (dfmRoundScale (2 ^ 64)
            (unadjustedStage20.foldBound quinticGoldilocksCard quinticGoldilocksCard_pos)))
        (merkleProfileQromBound prof (2 ^ 64))) := by
    let a := RatBound.scale 131071
      (dfmRoundScale (2 ^ 64)
        (unadjustedStage20.foldBound quinticGoldilocksCard quinticGoldilocksCard_pos))
    let b := merkleProfileQromBound prof (2 ^ 64)
    show a.num * (a.den * b.den) ≤ (a.num * b.den + b.num * a.den) * a.den
    have e : a.num * (a.den * b.den) = a.num * b.den * a.den := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [e]; exact Nat.mul_le_mul_right a.den (Nat.le_add_right _ _)
  have hBad := ratBound_lt_of_le_of_lt_packed hSub hLt
  rw [WhirStage.foldBound_eq] at hBad
  revert hBad
  unfold dfmRoundScale RatBound.scale RatBound.lt RatBound.invPow2 unadjustedStage20
  decide +kernel

theorem inhabited_packedFiberCerts :
    ∃ (prof : WhirCommitmentProfile) (logCells Q : Nat),
      16 ≤ logCells ∧ logCells ≤ 28 ∧ Q ≤ 2 ^ 64 ∧
      0 < (merkleProfileQromBound prof Q).den ∧
      (packedProdSched logCells).johnsonOk = true :=
  ⟨.poseidon2Gl24, 20, 2 ^ 64, by decide, by decide, Nat.le_refl _,
   (merkleProfileQromBound .poseidon2Gl24 (2 ^ 64)).h_pos, by decide +kernel⟩

theorem inhabited_recursiveMargin_tree :
    ∃ (prof : WhirCommitmentProfile) (d Q : Nat),
      d ≤ 16 ∧ Q ≤ 2 ^ 64 ∧
      0 < (merkleProfileQromBound prof Q).den ∧
      zkHemV2RecursiveMarginSched.johnsonOk = true :=
  ⟨.poseidon2Gl24, 16, 2 ^ 64, Nat.le_refl _, Nat.le_refl _,
   (merkleProfileQromBound .poseidon2Gl24 (2 ^ 64)).h_pos,
   zkHemV2RecursiveMarginSched_johnson_and_dkt26.1⟩

#verify_constructive
  Qsag.ZkHemV2Packed.poseidon2Gl24DigestCard_gt_2pow447
  Qsag.ZkHemV2Packed.merkleProfileQromBound_le_400
  Qsag.ZkHemV2Packed.merkleProfileQromBound_mono
  Qsag.ZkHemV2Packed.encodeQuinticNat_lt
  Qsag.ZkHemV2Packed.encodeQuinticNat_decodeQuinticNat
  Qsag.ZkHemV2Packed.decodeQuinticNat_encodeQuinticNat
  Qsag.ZkHemV2Packed.packedProdQromError_16_covers_two_guesses
  Qsag.ZkHemV2Packed.packedProdQromError_eq
  Qsag.ZkHemV2Packed.packedStagesRoundBounds_length
  Qsag.ZkHemV2Packed.decodeQuintic400_preimage_le
  Qsag.ZkHemV2Packed.gsList_single_ood_bad_seeds_le
  Qsag.ZkHemV2Packed.packedProdSched_johnsonOk
  Qsag.ZkHemV2Packed.packed_stage_accepts_logDomain_path
  Qsag.ZkHemV2Packed.tooth_scalar_stage_rejects_logDomain_path
  Qsag.ZkHemV2Packed.deployed_single_ood_gs_bad_lt_277
  Qsag.ZkHemV2Packed.zkHemV2_packed_all13_qrom_lt_128_at_2pow64
  Qsag.ZkHemV2Packed.zkHemV2RecursiveMarginSched_johnson_and_dkt26
  Qsag.ZkHemV2Packed.zkHemV2RecursiveMargin_tree_lt_128
  Qsag.ZkHemV2Packed.tooth_unadjusted_single_sched_fails_d16
  Qsag.ZkHemV2Packed.inhabited_packedFiberCerts
  Qsag.ZkHemV2Packed.inhabited_recursiveMargin_tree

#verify_inhabited
  Qsag.ZkHemV2Packed.zkHemV2_packed_all13_qrom_lt_128_at_2pow64
  Qsag.ZkHemV2Packed.inhabited_packedFiberCerts
#verify_inhabited
  Qsag.ZkHemV2Packed.zkHemV2RecursiveMargin_tree_lt_128
  Qsag.ZkHemV2Packed.inhabited_recursiveMargin_tree

#tooth_pair Qsag.ZkHemV2Packed.packed_stage_accepts_logDomain_path vs
  Qsag.ZkHemV2Packed.tooth_scalar_stage_rejects_logDomain_path
#tooth_pair Qsag.ZkHemV2Packed.zkHemV2RecursiveMargin_tree_lt_128 vs
  Qsag.ZkHemV2Packed.tooth_unadjusted_single_sched_fails_d16

end Qsag.ZkHemV2Packed
end

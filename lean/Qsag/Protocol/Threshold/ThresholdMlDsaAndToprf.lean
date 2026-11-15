module
/-
# Threshold ML-DSA arithmetic, checked signing, TOPRF execution, and credential relations

Proved here, constructively:

* The 256-point negacyclic NTT with its inverse (`fips204InvNtt_ntt`, `fips204Ntt_invNtt`),
  field arithmetic, rounding identities, and a coset LDE that interpolates through the
  inverse NTT (`cosetLde204_ntt`) on a validated domain (`cosetDomain204_inhabited`).
* `mldsaVerify` is the parameterized algebraic core kept for the MIR bridge.
  `mldsaVerifyBytes204` is the standalone ML-DSA-44 verifier on wire bytes (SHAKE, ExpandA,
  SampleInBall, packing, strict signature and hint decoding); it fails closed when a
  rejection sampler exhausts its byte budget. Agreement with other implementations is an
  executed check, not a theorem.
* Signing consumes multiplication results through a transcript-computed sacrifice check
  (`rssSacrificedSignStep`): an accepted attempt equals the exact-product reference
  transition unless the challenge lies in a list of bad values fixed by the transcript
  (`rssSacrificedSignStep_refines`). `rssDurableSign204` reserves the aggregate nonce in a
  persistent ledger before anything is released and releases only a final signature;
  nonces of released signatures are pairwise distinct across signs, failed writes and
  crashes (`rssDurable204_released_nonces_distinct`).
* The DKG is a commit, freeze, reveal machine; after freezing, the share accepted at each
  position is fixed up to a hash collision (`dkg204_reveal_determined_at_freeze`).
* The TOPRF client output is derived through decoded holder messages at every
  multiplication of all 30 rounds, for the full-value transport unconditionally
  (`toprfActiveClient204_correct`) and for the digest transport up to a collision.
  `toprf_joint_view_simulation` gives one coin bijection for the input sharing and all
  gates together.

* The verification extension `F_q[X]/(X^6 - 7)` is a field: Frobenius acts on coordinates
  (`ext6Pow_frobenius`), every nonzero element has the executable inverse `ext6Inv`
  (`ext6Mul_inv_cancel`), products vanish only at zero (`ext6Mul_eq_zero`), and the modulus
  has no proper factorization (`ext6Modulus_irreducible`).

* Batching and folding coins of the multiplication check are extension elements; a
  discrepancy polynomial over the extension has at most degree-many roots among them
  (`rss_ext6_discrepancy_roots_le`).
* Replacing every key-expanded mask tape by an independent tape costs the number of keys
  times the single-key distinguishing bound (`prss_multi_key_hybrid`).

Companion security modules: `Qsag.ThresholdMlDsaSecurity` proves 3-party `(2, 3)` RSS
multiplication and repeated-sacrifice refinement (`rss3MulStep_recon`,
`rss3_repeated_sacrifice_pq256`, `rss_distributed_trace_refines_sacrificedSignStep`),
multi-attempt sealed-`w₁` abort-transcript zero-knowledge (`threshold_mldsa_abort_transcript_zk`),
and `ML-DSA-65`/`87` (`PQ128`) parameter bounds (`mlDsa_challenge_entropy_bounds`), while
`Qsag.BlindVcQromSecurity` proves `438`-repetition `BlindVC` QROM Fiat-Shamir soundness
(`blindVc_quantum128_qrom_fs_soundness`) and issuer `ML-DSA` root-attestation unforgeability
(`blindVc_presentation_reduces_to_issuer_mldsa`). The single-key PRF assumption on PRSS tape
expansion and Rust wire-bytes transcript equivalence remain external to the algebraic model.
-/

public import Qsag.Protocol.Threshold.MlDsa44Parameters
public import Qsag.Math.Constructive
public import Qsag.Exec.SimulationSpine
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.UcGames
public import Qsag.Protocol.Credentials.AdvancedMpcAndCreds
public import Qsag.Coding.AffineProximityGaps
public import Qsag.Tactic.AssuranceKit
import all Qsag.Protocol.Credentials.AdvancedMpcAndCreds
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Math.Goldilocks

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false

/-! ## §1. Exact NIST FIPS 204 (`ML-DSA-44`) Field, 256-Point Negacyclic NTT & Rounding Laws -/

/-- NIST FIPS 204 prime modulus $q = 8380417 = 2^{23} - 2^{13} + 1 = 1023 \cdot 2^{13} + 1$. -/
@[expose] def mldsaQ : Nat := 8380417

/-- Cyclotomic ring degree $N = 256$. -/
def mldsaN : Nat := 256

/-- Dropped public-key low-order bit width $d = 13$ ($2^{13} = 8192$). -/
def mldsaD : Nat := 13

/-- Primitive 512-th root of unity $\zeta = 1753 \in \mathbb{Z}_q$ ($\zeta^{256} \equiv -1 \pmod q$). -/
def mldsaZetaNat : Nat := 1753

/-- `ML-DSA-44` (`FIPS 204` Category 2) parameter constants. -/
def mldsa44Gamma2 : Nat := 95232        -- (q - 1) / 88
def mldsa44Alpha : Nat := 190464        -- 2 * gamma2 = (q - 1) / 44
def mldsa44HighMod : Nat := 44          -- (q - 1) / alpha
def mldsa44Tau : Nat := 39
def mldsa44Eta : Nat := 2
def mldsa44Omega : Nat := 80
def mldsa44K : Nat := 4
def mldsa44L : Nat := 4

/-! ### §1.1 Constructive Primality Certificate for `mldsaQ = 8380417` -/

/-- Exported primality witness structure on `Nat` (`0` `@[expose]` overhead). -/
structure IsPrime204 (p : Nat) : Prop where
  ge_two : 2 ≤ p
  dvd_cases : ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

private def noDivTree (n lo : Nat) : Nat → Bool
  | 0 => (n % lo != 0)
  | d + 1 => noDivTree n lo d && noDivTree n (lo + 2 ^ d) d

private theorem noDivTree_sound :
    ∀ (d n lo : Nat), noDivTree n lo d = true →
      ∀ k : Nat, lo ≤ k → k < lo + 2 ^ d → ¬ (k ∣ n)
  | 0, n, lo, hok, k, hlo, hhi, hdvd => by
    have hk : k = lo := by simp at hhi; omega
    subst hk
    simp only [noDivTree, bne_iff_ne] at hok
    exact hok (Nat.mod_eq_zero_of_dvd hdvd)
  | d + 1, n, lo, hok, k, hlo, hhi, hdvd => by
    simp only [noDivTree, Bool.and_eq_true] at hok
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    if hmid : k < lo + 2 ^ d then
      exact noDivTree_sound d n lo hok.1 k hlo hmid hdvd
    else
      exact noDivTree_sound d n (lo + 2 ^ d) hok.2 k (by omega) (by omega) hdvd

private theorem mldsaQ_no_small_div : noDivTree mldsaQ 2 12 = true := by decide

/-- Every divisor of `mldsaQ = 8380417` is `1` or `8380417` ($\lfloor\sqrt{8380417}\rfloor = 2894 < 2 + 2^{12}$). -/
theorem mldsaQ_dvd_cases (d : Nat) (hd : d ∣ mldsaQ) :
    d = 1 ∨ d = mldsaQ := by
  if hd1 : d = 1 then exact .inl hd1
  else if hdq : d = mldsaQ then exact .inr hdq
  else
    exfalso
    obtain ⟨e, he⟩ := hd
    have hdPos : 2 ≤ d := by
      if hd0 : d = 0 then subst hd0; simp [mldsaQ] at he
      else omega
    have hePos : 2 ≤ e := by
      if he0 : e = 0 then subst he0; simp [mldsaQ] at he
      else if he1 : e = 1 then subst he1; simp at he; exact False.elim (hdq he.symm)
      else omega
    have hno := noDivTree_sound 12 mldsaQ 2 mldsaQ_no_small_div
    have h2pow12 : (2 : Nat) + 2 ^ 12 = 4098 := rfl
    rw [h2pow12] at hno
    if hle : d ≤ e then
      have hdLt : d < 2896 := by
        if hge : 2896 ≤ d then
          have hsq : 2896 * 2896 ≤ d * e := Nat.mul_le_mul hge (Nat.le_trans hge hle)
          unfold mldsaQ at he; omega
        else omega
      exact hno d hdPos (by omega) ⟨e, he⟩
    else
      have heLt : e < 2896 := by
        if hge : 2896 ≤ e then
          have hsq : 2896 * 2896 ≤ d * e := Nat.mul_le_mul (by omega) hge
          unfold mldsaQ at he; omega
        else omega
      exact hno e hePos (by omega) ⟨d, Nat.mul_comm d e ▸ he⟩

/-- **Constructive Primality of FIPS 204 Modulus `mldsaQ = 8380417`**. -/
theorem mldsaQ_isPrime : IsPrime204 mldsaQ :=
  ⟨by decide, mldsaQ_dvd_cases⟩

theorem IsPrime204.dvd_mul {p a b : Nat} (hp : IsPrime204 p)
    (hdvd : p ∣ a * b) (hna : ¬ (p ∣ a)) : p ∣ b := by
  obtain ⟨hda, hdp⟩ := extGcd_dvd a p
  have hg1 : (extGcd a p).1 = 1 := by
    rcases hp.dvd_cases _ hdp with h1 | hpp
    · exact h1
    · rw [hpp] at hda; exact False.elim (hna hda)
  have hbez := extGcd_bezout a p
  rw [hg1] at hbez
  obtain ⟨k, hk⟩ := hdvd
  have hmul : ((a : Int) * (extGcd a p).2.1 + (p : Int) * (extGcd a p).2.2) * (b : Int) =
      1 * (b : Int) := congrArg (· * (b : Int)) hbez
  rw [Int.add_mul, Int.one_mul] at hmul
  have hab : (a : Int) * (extGcd a p).2.1 * (b : Int) =
      (p : Int) * ((k : Int) * (extGcd a p).2.1) := by
    have hkInt : (a : Int) * (b : Int) = (p : Int) * (k : Int) := by exact_mod_cast hk
    rw [Int.mul_right_comm (a : Int), hkInt, Int.mul_assoc]
  rw [hab, Int.mul_assoc (p : Int), ← Int.mul_add] at hmul
  exact Int.ofNat_dvd.1 ⟨(k : Int) * (extGcd a p).2.1 + (extGcd a p).2.2 * (b : Int), hmul.symm⟩

/-! ### §1.2 Canonical Field `Fq204`, Barrett Multiplication & Constructive Bézout Inversion -/

/-- Canonical element of $\mathbb{Z}_q$ ($q = 8380417$). -/
structure Fq204 where
  val : Nat
  isLt : val < mldsaQ
  deriving DecidableEq, Repr

namespace Fq204

theorem ext {a b : Fq204} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

@[expose] def ofNat (n : Nat) : Fq204 :=
  ⟨n % mldsaQ, Nat.mod_lt n (by decide)⟩

def zero : Fq204 := ⟨0, by decide⟩
def one : Fq204 := ⟨1, by decide⟩

instance : Inhabited Fq204 := ⟨zero⟩

@[simp] theorem zero_val : zero.val = 0 := by rfl
@[simp] theorem one_val : one.val = 1 := by rfl
@[simp] theorem ofNat_val (n : Nat) : (ofNat n).val = n % mldsaQ := by rfl

def add (a b : Fq204) : Fq204 :=
  if h : a.val + b.val < mldsaQ then
    ⟨a.val + b.val, h⟩
  else
    ⟨a.val + b.val - mldsaQ, by have := a.isLt; have := b.isLt; omega⟩

theorem add_val (a b : Fq204) : (add a b).val = (a.val + b.val) % mldsaQ := by
  unfold add
  have ha := a.isLt; have hb := b.isLt
  if hlt : a.val + b.val < mldsaQ then
    simp only [hlt, ↓reduceDIte]
    exact (Nat.mod_eq_of_lt hlt).symm
  else
    simp only [hlt, ↓reduceDIte]
    have hEq : a.val + b.val = (a.val + b.val - mldsaQ) + mldsaQ * 1 := by omega
    conv => rhs; rw [hEq, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt (by omega)).symm

def neg (a : Fq204) : Fq204 :=
  if h : a.val = 0 then ⟨0, by decide⟩ else ⟨mldsaQ - a.val, by have := a.isLt; omega⟩

theorem neg_val (a : Fq204) : (neg a).val = (mldsaQ - a.val) % mldsaQ := by
  unfold neg
  have ha := a.isLt
  if h0 : a.val = 0 then
    simp [h0]
  else
    simp only [h0, ↓reduceDIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

def sub (a b : Fq204) : Fq204 :=
  if h : b.val ≤ a.val then
    ⟨a.val - b.val, by have := a.isLt; omega⟩
  else
    ⟨a.val + mldsaQ - b.val, by have := a.isLt; have := b.isLt; omega⟩

theorem sub_val (a b : Fq204) : (sub a b).val = (a.val + mldsaQ - b.val) % mldsaQ := by
  unfold sub
  have ha := a.isLt; have hb := b.isLt
  if hle : b.val ≤ a.val then
    simp only [hle, ↓reduceDIte]
    have hEq : a.val + mldsaQ - b.val = (a.val - b.val) + mldsaQ * 1 := by omega
    conv => rhs; rw [hEq, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  else
    simp only [hle, ↓reduceDIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

def mul (a b : Fq204) : Fq204 :=
  ⟨(a.val * b.val) % mldsaQ, Nat.mod_lt _ (by decide)⟩

@[simp] theorem mul_val (a b : Fq204) : (mul a b).val = (a.val * b.val) % mldsaQ := by rfl

theorem add_assoc (a b c : Fq204) : add (add a b) c = add a (add b c) :=
  ext <| by rw [add_val, add_val, add_val, add_val, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem add_comm (a b : Fq204) : add a b = add b a :=
  ext <| by rw [add_val, add_val, Nat.add_comm]

theorem zero_add (a : Fq204) : add zero a = a :=
  ext <| by rw [add_val, zero_val, Nat.zero_add, Nat.mod_eq_of_lt a.isLt]

theorem add_zero (a : Fq204) : add a zero = a :=
  ext <| by rw [add_val, zero_val, Nat.add_zero, Nat.mod_eq_of_lt a.isLt]

theorem add_left_neg (a : Fq204) : add (neg a) a = zero :=
  ext <| by
    rw [add_val, neg_val, Nat.mod_add_mod]
    have ha := a.isLt
    have hEq : mldsaQ - a.val + a.val = mldsaQ := by omega
    rw [hEq, Nat.mod_self, zero_val]

theorem add_right_neg (a : Fq204) : add a (neg a) = zero := by
  rw [add_comm, add_left_neg]

theorem sub_eq_add_neg (a b : Fq204) : sub a b = add a (neg b) :=
  ext <| by
    rw [sub_val, add_val, neg_val, Nat.add_mod_mod]
    have hb := b.isLt
    have hEq : a.val + (mldsaQ - b.val) = a.val + mldsaQ - b.val := by omega
    rw [hEq]

theorem mul_assoc (a b c : Fq204) : mul (mul a b) c = mul a (mul b c) :=
  ext <| by rw [mul_val, mul_val, mul_val, mul_val, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

theorem mul_comm (a b : Fq204) : mul a b = mul b a :=
  ext <| by rw [mul_val, mul_val, Nat.mul_comm]

theorem one_mul (a : Fq204) : mul one a = a :=
  ext <| by rw [mul_val, one_val, Nat.one_mul, Nat.mod_eq_of_lt a.isLt]

theorem mul_one (a : Fq204) : mul a one = a :=
  ext <| by rw [mul_val, one_val, Nat.mul_one, Nat.mod_eq_of_lt a.isLt]

theorem mul_zero (a : Fq204) : mul a zero = zero :=
  ext <| by rw [mul_val, zero_val, Nat.mul_zero, Nat.zero_mod]

theorem zero_mul (a : Fq204) : mul zero a = zero :=
  ext <| by rw [mul_val, zero_val, Nat.zero_mul, Nat.zero_mod]

theorem left_distrib (a b c : Fq204) : mul a (add b c) = add (mul a b) (mul a c) :=
  ext <| by
    rw [mul_val, add_val, add_val, mul_val, mul_val,
        Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.left_distrib, Nat.add_mod]

theorem right_distrib (a b c : Fq204) : mul (add a b) c = add (mul a c) (mul b c) :=
  ext <| by
    rw [mul_val, add_val, add_val, mul_val, mul_val,
        Nat.mod_mul_mod, Nat.right_distrib, Nat.add_mod]

theorem add_left_cancel {a b c : Fq204} (h : add a b = add a c) : b = c := by
  have h1 := congrArg (add (neg a)) h
  rwa [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1

theorem sub_zero (a : Fq204) : sub a zero = a := by
  apply ext
  rw [sub_val, zero_val]
  have ha := a.isLt
  have hEq : a.val + mldsaQ - 0 = a.val + mldsaQ * 1 := by omega
  rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem mul_neg (a b : Fq204) : mul a (neg b) = neg (mul a b) := by
  apply add_left_cancel (a := mul a b)
  rw [← left_distrib, add_right_neg, mul_zero, add_right_neg]

theorem neg_add (a b : Fq204) : neg (add a b) = add (neg a) (neg b) := by
  apply add_left_cancel (a := add a b)
  rw [add_right_neg, add_assoc a b, ← add_assoc b (neg a), add_comm b (neg a),
      add_assoc (neg a) b, add_right_neg, add_zero, add_right_neg]

def ofInt (z : Int) : Fq204 :=
  ⟨(z % (mldsaQ : Int)).toNat, by
    have := Int.emod_nonneg z (show (mldsaQ : Int) ≠ 0 by decide)
    have := Int.emod_lt_of_pos z (show (0 : Int) < mldsaQ by decide)
    omega⟩

theorem ofInt_val (z : Int) : ((ofInt z).val : Int) = z % (mldsaQ : Int) :=
  Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))

theorem ofInt_nat (a : Fq204) : ofInt (a.val : Int) = a := by
  apply ext; apply Int.ofNat_inj.mp
  rw [ofInt_val]
  exact Int.emod_eq_of_lt (by omega) (by have := a.isLt; omega)

theorem add_int (a b : Fq204) :
    ((add a b).val : Int) = ((a.val : Int) + (b.val : Int)) % (mldsaQ : Int) := by
  rw [add_val, Int.natCast_emod, Int.natCast_add]

theorem sub_int (a b : Fq204) :
    ((sub a b).val : Int) = ((a.val : Int) - (b.val : Int)) % (mldsaQ : Int) := by
  rw [sub_val, Int.natCast_emod, Int.ofNat_sub (by have := b.isLt; omega), Int.natCast_add]
  have he : (a.val : Int) + (mldsaQ : Int) - (b.val : Int) =
      ((a.val : Int) - (b.val : Int)) + (mldsaQ : Int) := by omega
  rw [he, Int.add_emod_right]

theorem mul_int (a b : Fq204) :
    ((mul a b).val : Int) = ((a.val : Int) * (b.val : Int)) % (mldsaQ : Int) := by
  rw [mul_val, Int.natCast_emod, Int.natCast_mul]

theorem ofInt_add (a b : Int) : add (ofInt a) (ofInt b) = ofInt (a + b) := by
  apply ext; apply Int.ofNat_inj.mp
  rw [add_int, ofInt_val, ofInt_val, ofInt_val, ← Int.add_emod]

theorem ofInt_sub (a b : Int) : sub (ofInt a) (ofInt b) = ofInt (a - b) := by
  apply ext; apply Int.ofNat_inj.mp
  rw [sub_int, ofInt_val, ofInt_val, ofInt_val, ← Int.sub_emod]

theorem ofInt_mul (a b : Int) : mul (ofInt a) (ofInt b) = ofInt (a * b) := by
  apply ext; apply Int.ofNat_inj.mp
  rw [mul_int, ofInt_val, ofInt_val, ofInt_val, ← Int.mul_emod]

theorem ofInt_neg (a : Int) : neg (ofInt a) = ofInt (-a) := by
  have h0 : ofInt 0 = zero := by decide
  apply add_left_cancel (a := ofInt a)
  rw [add_right_neg, ofInt_add]
  have hz : a + (-a) = 0 := by omega
  rw [hz, h0]

/-- Centered representative in $(-q/2, q/2] = [-4190208, 4190208]$. -/
def toCenteredInt (a : Fq204) : Int :=
  if a.val ≤ mldsaQ / 2 then (a.val : Int) else (a.val : Int) - (mldsaQ : Int)

/-- Infinity-norm magnitude $|a \bmod^\pm q| \in [0, 4190208]$. -/
def centeredAbs (a : Fq204) : Nat :=
  if a.val ≤ mldsaQ / 2 then a.val else mldsaQ - a.val

theorem ofInt_toCenteredInt (a : Fq204) : ofInt (toCenteredInt a) = a := by
  apply ext; apply Int.ofNat_inj.mp
  rw [ofInt_val]; unfold toCenteredInt
  have ha := a.isLt
  split
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · have hEq : ((a.val : Int) - (mldsaQ : Int)) + (mldsaQ : Int) = (a.val : Int) := by omega
    rw [← Int.add_emod_right ((a.val : Int) - (mldsaQ : Int)) (mldsaQ : Int), hEq]
    exact Int.emod_eq_of_lt (by omega) (by omega)

theorem toCenteredInt_natAbs (a : Fq204) : (toCenteredInt a).natAbs = centeredAbs a := by
  unfold toCenteredInt centeredAbs
  have ha := a.isLt
  split <;> omega

theorem toCenteredInt_ofInt_eq {z : Int} (hLo : -4190208 ≤ z) (hHi : z ≤ 4190208) :
    toCenteredInt (ofInt z) = z := by
  unfold toCenteredInt
  have hv : ((ofInt z).val : Int) = z % (8380417 : Int) := ofInt_val z
  unfold mldsaQ
  if hz : 0 ≤ z then
    have hmod : z % (8380417 : Int) = z := Int.emod_eq_of_lt hz (by omega)
    rw [hmod] at hv
    split <;> omega
  else
    have hmod : z % (8380417 : Int) = z + 8380417 := by
      rw [← Int.add_emod_right z (8380417 : Int)]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod] at hv
    split <;> omega

end Fq204

/-- Division-free 64-bit Barrett modular multiplication (`fips204_ntt.rs:fq_mul`). -/
def fqMulBarrettSpec (a b : Nat) : Nat :=
  let barrettM64 : Nat := 18446744073709551616 / mldsaQ  -- 2_201_154_512_929
  let prod := a * b
  let qEst := (prod * barrettM64) / 18446744073709551616
  let rem := prod - qEst * mldsaQ
  if rem < mldsaQ then rem else rem - mldsaQ

/-- **`fqMulBarrett_sound`**: hardware-exact 64-bit Barrett multiplication equals `(a * b) % q`
    for all `a, b < 8380417` with zero division instructions and zero underflow. -/
theorem fqMulBarrett_sound {a b : Nat} (ha : a < mldsaQ) (hb : b < mldsaQ) :
    fqMulBarrettSpec a b = (a * b) % mldsaQ := by
  unfold fqMulBarrettSpec mldsaQ at *
  have hprod : a * b ≤ 8380416 * 8380416 := Nat.mul_le_mul (by omega) (by omega)
  dsimp only
  split <;> omega

instance : CommRingOps Fq204 where
  zero := Fq204.zero
  one := Fq204.one
  add := Fq204.add
  mul := Fq204.mul
  neg := Fq204.neg
  sub := Fq204.sub

instance : LawfulCommRing Fq204 where
  add_assoc := Fq204.add_assoc
  add_comm := Fq204.add_comm
  zero_add := Fq204.zero_add
  add_zero := Fq204.add_zero
  add_left_neg := Fq204.add_left_neg
  sub_eq_add_neg := Fq204.sub_eq_add_neg
  mul_assoc := Fq204.mul_assoc
  mul_comm := Fq204.mul_comm
  one_mul := Fq204.one_mul
  mul_one := Fq204.mul_one
  left_distrib := Fq204.left_distrib
  right_distrib := Fq204.right_distrib

instance : NoZeroDivisors Fq204 where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have hval : (a.val * b.val) % mldsaQ = 0 := congrArg Fq204.val h
    have hdvd : mldsaQ ∣ a.val * b.val := Nat.dvd_of_mod_eq_zero hval
    if ha0 : a.val = 0 then
      exact .inl (Fq204.ext ha0)
    else
      have hna : ¬ (mldsaQ ∣ a.val) := fun hda => by
        have hle := Nat.le_of_dvd (by omega) hda
        have := a.isLt; omega
      have hdb := mldsaQ_isPrime.dvd_mul hdvd hna
      if hb0 : b.val = 0 then
        exact .inr (Fq204.ext hb0)
      else
        have hle := Nat.le_of_dvd (by omega) hdb
        have := b.isLt; omega

namespace Fq204

/-- Field power $a^e \in \mathbb{Z}_q$. -/
def pow (a : Fq204) : Nat → Fq204
  | 0 => one
  | k + 1 => mul (pow a k) a

@[simp] theorem pow_val (a : Fq204) : ∀ k : Nat, (pow a k).val = (a.val ^ k) % mldsaQ
  | 0 => by rfl
  | k + 1 => by
    dsimp only [pow]
    rw [mul_val, pow_val a k, Nat.pow_succ, Nat.mod_mul_mod]

theorem pow_add (a : Fq204) (m n : Nat) : pow a (m + n) = mul (pow a m) (pow a n) := by
  apply ext; rw [pow_val, mul_val, pow_val, pow_val, ← Nat.mul_mod, ← Nat.pow_add]

theorem pow_mul (a : Fq204) (m n : Nat) : pow a (m * n) = pow (pow a m) n := by
  induction n with
  | zero => dsimp only [Nat.mul_zero, pow]
  | succ n ih => rw [Nat.mul_succ, pow_add, ih]; dsimp only [pow]

/-- Constructive Bézout field inverse via `extGcd` (`0 ↦ 0`). -/
def inv (a : Fq204) : Fq204 :=
  if a.val = 0 then zero else ofInt (extGcd a.val mldsaQ).2.1

/-- **`Fq204.mul_inv_cancel`**: every nonzero element in $\mathbb{Z}_{8380417}$ has a multiplicative inverse. -/
theorem mul_inv_cancel {a : Fq204} (ha : a ≠ zero) : mul a (inv a) = one := by
  have ha0 : a.val ≠ 0 := fun hz => ha (ext hz)
  unfold inv
  simp only [ha0, ↓reduceIte]
  obtain ⟨hda, hdq⟩ := extGcd_dvd a.val mldsaQ
  have hg1 : (extGcd a.val mldsaQ).1 = 1 := by
    rcases mldsaQ_isPrime.dvd_cases _ hdq with h1 | hqq
    · exact h1
    · rw [hqq] at hda
      have hle := Nat.le_of_dvd (by omega) hda
      have := a.isLt; omega
  have hbez := extGcd_bezout a.val mldsaQ
  rw [hg1] at hbez
  generalize hx : (extGcd a.val mldsaQ).2.1 = x at hbez ⊢
  generalize hy : (extGcd a.val mldsaQ).2.2 = y at hbez
  rw [← ofInt_nat a, ofInt_mul]
  apply ext; apply Int.ofNat_inj.mp
  rw [ofInt_val, one_val]
  have hEq : (a.val : Int) * x = (1 : Int) + (mldsaQ : Int) * (-y) := by
    rw [Int.mul_neg]
    omega
  rw [hEq, Int.add_mul_emod_self_left]
  decide

theorem inv_mul_cancel {a : Fq204} (ha : a ≠ zero) : mul (inv a) a = one := by
  rw [mul_comm, mul_inv_cancel ha]

end Fq204

instance : LawfulField Fq204 where
  inv := Fq204.inv
  zero_ne_one := by decide
  mul_inv_cancel := Fq204.mul_inv_cancel

/-! ### §1.3 256-Point Negacyclic Ring $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$ & 8-Stage NTT Isomorphism -/

/-- Primitive 512-th root $\zeta = 1753 \in \mathbb{Z}_{8380417}$. -/
def mldsaZeta : Fq204 := ⟨1753, by decide⟩

/-- Multiplicative inverse $2^{-1} \equiv 4190209 \pmod{8380417}$. -/
def mldsaInv2 : Fq204 := ⟨4190209, by decide⟩

/-- Multiplicative inverse $256^{-1} \equiv 8347681 \pmod{8380417}$. -/
def mldsaInv256 : Fq204 := ⟨8347681, by decide⟩

private theorem fq204_sq_eq_pow2 (a : Fq204) : Fq204.pow a 2 = Fq204.mul a a := by
  dsimp only [Fq204.pow]; rw [Fq204.one_mul]

theorem mldsaZeta_pow256_eq_neg_one :
    Fq204.pow mldsaZeta 256 = Fq204.neg Fq204.one := by
  have h256 : (256 : Nat) = 2 * (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) := rfl
  rw [h256, Fq204.pow_mul, Fq204.pow_mul, Fq204.pow_mul, Fq204.pow_mul,
      Fq204.pow_mul, Fq204.pow_mul, Fq204.pow_mul,
      fq204_sq_eq_pow2, fq204_sq_eq_pow2, fq204_sq_eq_pow2, fq204_sq_eq_pow2,
      fq204_sq_eq_pow2, fq204_sq_eq_pow2, fq204_sq_eq_pow2, fq204_sq_eq_pow2]
  decide

theorem mldsaZeta_pow512_eq_one :
    Fq204.pow mldsaZeta 512 = Fq204.one := by
  have h512 : (512 : Nat) = 256 * 2 := rfl
  rw [h512, Fq204.pow_mul, mldsaZeta_pow256_eq_neg_one]
  decide

theorem mldsa_two_mul_inv2 : Fq204.mul (Fq204.ofNat 2) mldsaInv2 = Fq204.one := by decide

/-- Inductive binary tree of $2^d$ field elements (`0` `module` opacity mismatch). -/
inductive PolyTree : Nat → Type where
  | leaf (x : Fq204) : PolyTree 0
  | branch {d : Nat} (lo hi : PolyTree d) : PolyTree (d + 1)
  deriving DecidableEq, Repr

/-- Exact 256-coefficient polynomial / NTT vector over $\mathbb{Z}_{8380417}$ ($2^8 = 256$). -/
abbrev Poly256 := PolyTree 8

namespace PolyTree

def zero : (d : Nat) → PolyTree d
  | 0 => .leaf Fq204.zero
  | d + 1 => .branch (zero d) (zero d)

def constUnit : (d : Nat) → PolyTree d
  | 0 => .leaf Fq204.one
  | d + 1 => .branch (constUnit d) (zero d)

def ones : (d : Nat) → PolyTree d
  | 0 => .leaf Fq204.one
  | d + 1 => .branch (ones d) (ones d)

instance (d : Nat) : Inhabited (PolyTree d) := ⟨zero d⟩

def add : {d : Nat} → PolyTree d → PolyTree d → PolyTree d
  | 0, .leaf a, .leaf b => .leaf (Fq204.add a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => .branch (add a0 b0) (add a1 b1)

def sub : {d : Nat} → PolyTree d → PolyTree d → PolyTree d
  | 0, .leaf a, .leaf b => .leaf (Fq204.sub a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => .branch (sub a0 b0) (sub a1 b1)

def neg : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf a => .leaf (Fq204.neg a)
  | _ + 1, .branch a0 a1 => .branch (neg a0) (neg a1)

def scale (k : Fq204) : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf a => .leaf (Fq204.mul k a)
  | _ + 1, .branch a0 a1 => .branch (scale k a0) (scale k a1)

def pointwiseMul : {d : Nat} → PolyTree d → PolyTree d → PolyTree d
  | 0, .leaf a, .leaf b => .leaf (Fq204.mul a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => .branch (pointwiseMul a0 b0) (pointwiseMul a1 b1)

def toList : {d : Nat} → PolyTree d → List Fq204
  | 0, .leaf x => [x]
  | _ + 1, .branch lo hi => toList lo ++ toList hi

@[simp] theorem length_toList : ∀ {d : Nat} (p : PolyTree d), (toList p).length = 2 ^ d
  | 0, .leaf _ => by rfl
  | d + 1, .branch lo hi => by
    simp only [toList, List.length_append, length_toList, Nat.pow_succ]
    omega

def ofList : (d : Nat) → List Fq204 → PolyTree d
  | 0, xs => .leaf (xs.headD Fq204.zero)
  | d + 1, xs =>
    let half := 2 ^ d
    .branch (ofList d (xs.take half)) (ofList d (xs.drop half))

theorem ofList_toList : ∀ {d : Nat} (p : PolyTree d), ofList d (toList p) = p
  | 0, .leaf _ => by rfl
  | d + 1, .branch lo hi => by
    simp only [toList, ofList]
    have hlen : (toList lo).length = 2 ^ d := length_toList lo
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
        List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
        List.nil_append, ofList_toList lo, ofList_toList hi]

theorem toList_ofList : ∀ {d : Nat} {xs : List Fq204}, xs.length = 2 ^ d → toList (ofList d xs) = xs
  | 0, xs, hlen => by
    cases xs with
    | nil => exact absurd hlen (by decide)
    | cons x rest =>
      cases rest with
      | nil => rfl
      | cons _ _ => simp only [List.length_cons] at hlen; omega
  | d + 1, xs, hlen => by
    simp only [ofList, toList]
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    have htake : (xs.take (2 ^ d)).length = 2 ^ d := by
      rw [List.length_take, hlen, hpow]; omega
    have hdrop : (xs.drop (2 ^ d)).length = 2 ^ d := by
      rw [List.length_drop, hlen, hpow]; omega
    rw [toList_ofList htake, toList_ofList hdrop, List.take_append_drop]

/-- Infinity norm $\max_{j} |p_j \bmod^\pm q|$ across all $2^d$ coefficients. -/
def infNorm : {d : Nat} → PolyTree d → Nat
  | 0, .leaf x => Fq204.centeredAbs x
  | _ + 1, .branch lo hi => max (infNorm lo) (infNorm hi)

/-- Taxicab ($\ell_1$) norm $\sum_j |p_j \bmod^\pm q|$. -/
def l1Norm : {d : Nat} → PolyTree d → Nat
  | 0, .leaf x => Fq204.centeredAbs x
  | _ + 1, .branch lo hi => l1Norm lo + l1Norm hi

/-- Leafwise predicate over a single `PolyTree d`. -/
def AllLeaves : {d : Nat} → (Fq204 → Prop) → PolyTree d → Prop
  | 0, P, .leaf a => P a
  | _ + 1, P, .branch a0 a1 => AllLeaves P a0 ∧ AllLeaves P a1

end PolyTree

/-- Exact 8-stage Cooley–Tukey radix-2 butterfly recursion (`fips204_ntt.rs:Poly256::ntt`). -/
def nttStage : (d : Nat) → Nat → PolyTree d → PolyTree d
  | 0, _, .leaf x => .leaf x
  | d + 1, e, .branch lo hi =>
    let z := Fq204.pow mldsaZeta (e / 2)
    let zh := PolyTree.scale z hi
    .branch (nttStage d (e / 2) (PolyTree.add lo zh))
            (nttStage d (e / 2 + 256) (PolyTree.sub lo zh))

/-- Exact 8-stage Gentleman–Sande inverse butterfly recursion (`fips204_ntt.rs:Poly256::inv_ntt`). -/
def invNttStage : (d : Nat) → Nat → PolyTree d → PolyTree d
  | 0, _, .leaf x => .leaf x
  | d + 1, e, .branch u v =>
    let u' := invNttStage d (e / 2) u
    let v' := invNttStage d (e / 2 + 256) v
    let zInv := Fq204.inv (Fq204.pow mldsaZeta (e / 2))
    .branch (PolyTree.scale mldsaInv2 (PolyTree.add u' v'))
            (PolyTree.scale (Fq204.mul mldsaInv2 zInv) (PolyTree.sub u' v'))

/-- Forward 256-point NIST FIPS 204 NTT (`Algorithm 41`). -/
def fips204Ntt (p : Poly256) : Poly256 := nttStage 8 256 p

/-- Inverse 256-point NIST FIPS 204 NTT (`Algorithm 42`). -/
def fips204InvNtt (u : Poly256) : Poly256 := invNttStage 8 256 u

private theorem mldsaZeta_pow_ne_zero (k : Nat) : Fq204.pow mldsaZeta k ≠ Fq204.zero := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro h0
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h0 with h1 | h2
    · exact ih h1
    · exact absurd h2 (by decide)

private theorem polyTree_butterfly_left_inv {d : Nat} (z : Fq204) (hz : z ≠ Fq204.zero)
    (lo hi : PolyTree d) :
    let zh := PolyTree.scale z hi
    let u := PolyTree.add lo zh
    let v := PolyTree.sub lo zh
    PolyTree.branch (PolyTree.scale mldsaInv2 (PolyTree.add u v))
      (PolyTree.scale (Fq204.mul mldsaInv2 (Fq204.inv z)) (PolyTree.sub u v)) =
      PolyTree.branch lo hi := by
  induction d with
  | zero =>
    cases lo with | leaf a =>
    cases hi with | leaf b =>
    dsimp only [PolyTree.scale, PolyTree.add, PolyTree.sub]
    have hTwo : Fq204.add Fq204.one Fq204.one = Fq204.ofNat 2 := by decide
    have h1 : Fq204.mul mldsaInv2 (Fq204.add (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b))) = a := by
      have hsum : Fq204.add (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b)) =
          Fq204.mul (Fq204.ofNat 2) a := by
        rw [Fq204.sub_eq_add_neg, Fq204.add_assoc a (Fq204.mul z b),
            ← Fq204.add_assoc (Fq204.mul z b) a, Fq204.add_comm (Fq204.mul z b) a,
            Fq204.add_assoc a (Fq204.mul z b), Fq204.add_right_neg, Fq204.add_zero]
        calc Fq204.add a a = Fq204.add (Fq204.mul Fq204.one a) (Fq204.mul Fq204.one a) := by
              rw [Fq204.one_mul]
        _ = Fq204.mul (Fq204.ofNat 2) a := by rw [← Fq204.right_distrib, hTwo]
      rw [hsum, ← Fq204.mul_assoc, Fq204.mul_comm mldsaInv2, mldsa_two_mul_inv2, Fq204.one_mul]
    have h2 : Fq204.mul (Fq204.mul mldsaInv2 (Fq204.inv z))
        (Fq204.sub (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b))) = b := by
      have hdiff : Fq204.sub (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b)) =
          Fq204.mul (Fq204.ofNat 2) (Fq204.mul z b) := by
        apply Fq204.add_left_cancel (a := Fq204.sub a (Fq204.mul z b))
        rw [Fq204.sub_eq_add_neg (Fq204.add a _), Fq204.add_comm (Fq204.sub a _),
            Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
        calc Fq204.add a (Fq204.mul z b)
          _ = Fq204.add (Fq204.sub a (Fq204.mul z b)) (Fq204.add (Fq204.mul z b) (Fq204.mul z b)) := by
            rw [Fq204.sub_eq_add_neg, Fq204.add_assoc, ← Fq204.add_assoc (Fq204.neg _),
                Fq204.add_left_neg, Fq204.zero_add]
          _ = Fq204.add (Fq204.sub a (Fq204.mul z b)) (Fq204.mul (Fq204.ofNat 2) (Fq204.mul z b)) := by
            congr 1
            calc Fq204.add (Fq204.mul z b) (Fq204.mul z b)
              _ = Fq204.add (Fq204.mul Fq204.one (Fq204.mul z b)) (Fq204.mul Fq204.one (Fq204.mul z b)) := by
                rw [Fq204.one_mul]
              _ = Fq204.mul (Fq204.ofNat 2) (Fq204.mul z b) := by rw [← Fq204.right_distrib, hTwo]
      rw [hdiff, Fq204.mul_comm mldsaInv2 (Fq204.inv z), Fq204.mul_assoc (Fq204.inv z) mldsaInv2,
          ← Fq204.mul_assoc mldsaInv2 (Fq204.ofNat 2), Fq204.mul_comm mldsaInv2 (Fq204.ofNat 2),
          mldsa_two_mul_inv2, Fq204.one_mul, ← Fq204.mul_assoc, Fq204.inv_mul_cancel hz, Fq204.one_mul]
    rw [h1, h2]
  | succ d ih =>
    cases lo with | branch lo0 lo1 =>
    cases hi with | branch hi0 hi1 =>
    have ih0 := PolyTree.branch.inj (ih lo0 hi0)
    have ih1 := PolyTree.branch.inj (ih lo1 hi1)
    simp only [PolyTree.scale, PolyTree.add, PolyTree.sub, ih0.1, ih1.1, ih0.2, ih1.2]

private theorem polyTree_butterfly_right_inv {d : Nat} (z : Fq204) (hz : z ≠ Fq204.zero)
    (u v : PolyTree d) :
    let lo := PolyTree.scale mldsaInv2 (PolyTree.add u v)
    let hi := PolyTree.scale (Fq204.mul mldsaInv2 (Fq204.inv z)) (PolyTree.sub u v)
    let zh := PolyTree.scale z hi
    PolyTree.branch (PolyTree.add lo zh) (PolyTree.sub lo zh) = PolyTree.branch u v := by
  induction d with
  | zero =>
    cases u with | leaf a =>
    cases v with | leaf b =>
    dsimp only [PolyTree.scale, PolyTree.add, PolyTree.sub]
    have hTwo : Fq204.add Fq204.one Fq204.one = Fq204.ofNat 2 := by decide
    have hzh : Fq204.mul z (Fq204.mul (Fq204.mul mldsaInv2 (Fq204.inv z)) (Fq204.sub a b)) =
        Fq204.mul mldsaInv2 (Fq204.sub a b) := by
      rw [Fq204.mul_comm mldsaInv2 (Fq204.inv z), ← Fq204.mul_assoc z,
          ← Fq204.mul_assoc z (Fq204.inv z), Fq204.mul_inv_cancel hz, Fq204.one_mul]
    rw [hzh, ← Fq204.left_distrib]
    have hsum : Fq204.add (Fq204.add a b) (Fq204.sub a b) = Fq204.mul (Fq204.ofNat 2) a := by
      rw [Fq204.sub_eq_add_neg, Fq204.add_assoc a b, ← Fq204.add_assoc b a,
          Fq204.add_comm b a, Fq204.add_assoc a b, Fq204.add_right_neg, Fq204.add_zero]
      calc Fq204.add a a = Fq204.add (Fq204.mul Fq204.one a) (Fq204.mul Fq204.one a) := by
            rw [Fq204.one_mul]
      _ = Fq204.mul (Fq204.ofNat 2) a := by rw [← Fq204.right_distrib, hTwo]
    have h1 : Fq204.mul mldsaInv2 (Fq204.add (Fq204.add a b) (Fq204.sub a b)) = a := by
      rw [hsum, ← Fq204.mul_assoc, Fq204.mul_comm mldsaInv2, mldsa_two_mul_inv2, Fq204.one_mul]
    have h2 : Fq204.sub (Fq204.mul mldsaInv2 (Fq204.add a b)) (Fq204.mul mldsaInv2 (Fq204.sub a b)) = b := by
      apply Fq204.add_left_cancel (a := Fq204.mul mldsaInv2 (Fq204.sub a b))
      rw [Fq204.sub_eq_add_neg (Fq204.mul mldsaInv2 (Fq204.add a b)),
          Fq204.add_comm (Fq204.mul mldsaInv2 (Fq204.sub a b)),
          Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
      calc Fq204.mul mldsaInv2 (Fq204.add a b)
        _ = Fq204.add (Fq204.mul mldsaInv2 (Fq204.sub a b)) (Fq204.mul mldsaInv2 (Fq204.add b b)) := by
          rw [← Fq204.left_distrib]
          congr 1
          rw [Fq204.sub_eq_add_neg, Fq204.add_assoc, ← Fq204.add_assoc (Fq204.neg b),
              Fq204.add_left_neg, Fq204.zero_add]
        _ = Fq204.add (Fq204.mul mldsaInv2 (Fq204.sub a b)) b := by
          congr 1
          have hbb : Fq204.add b b = Fq204.mul (Fq204.ofNat 2) b := by
            calc Fq204.add b b = Fq204.add (Fq204.mul Fq204.one b) (Fq204.mul Fq204.one b) := by
                  rw [Fq204.one_mul]
            _ = Fq204.mul (Fq204.ofNat 2) b := by rw [← Fq204.right_distrib, hTwo]
          rw [hbb, ← Fq204.mul_assoc, Fq204.mul_comm mldsaInv2, mldsa_two_mul_inv2, Fq204.one_mul]
    rw [h1, h2]
  | succ d ih =>
    cases u with | branch u0 u1 =>
    cases v with | branch v0 v1 =>
    have ih0 := PolyTree.branch.inj (ih u0 v0)
    have ih1 := PolyTree.branch.inj (ih u1 v1)
    simp only [PolyTree.scale, PolyTree.add, PolyTree.sub, ih0.1, ih1.1, ih0.2, ih1.2]

private theorem invNttStage_nttStage : ∀ (d e : Nat) (p : PolyTree d),
    invNttStage d e (nttStage d e p) = p
  | 0, _, .leaf _ => rfl
  | d + 1, e, .branch lo hi => by
    simp only [nttStage, invNttStage, invNttStage_nttStage d]
    exact polyTree_butterfly_left_inv (Fq204.pow mldsaZeta (e / 2)) (mldsaZeta_pow_ne_zero _) lo hi

private theorem nttStage_invNttStage : ∀ (d e : Nat) (u : PolyTree d),
    nttStage d e (invNttStage d e u) = u
  | 0, _, .leaf _ => rfl
  | d + 1, e, .branch u v => by
    simp only [invNttStage]
    have h := PolyTree.branch.inj <|
      polyTree_butterfly_right_inv (Fq204.pow mldsaZeta (e / 2)) (mldsaZeta_pow_ne_zero _)
        (invNttStage d (e / 2) u) (invNttStage d (e / 2 + 256) v)
    simp only [nttStage, h.1, h.2, nttStage_invNttStage d]

/-- **`fips204InvNtt_ntt`**: 256-point FIPS 204 inverse NTT left-inverts forward NTT. -/
theorem fips204InvNtt_ntt (p : Poly256) : fips204InvNtt (fips204Ntt p) = p :=
  invNttStage_nttStage 8 256 p

/-- **`fips204Ntt_invNtt`**: 256-point FIPS 204 forward NTT right-inverts inverse NTT. -/
theorem fips204Ntt_invNtt (u : Poly256) : fips204Ntt (fips204InvNtt u) = u :=
  nttStage_invNttStage 8 256 u

/-! #### Coefficient-Domain Polynomial Evaluation & Negacyclic Convolution -/

/-- Horner polynomial evaluation $\sum_{j=0}^{m-1} p_j \omega^j$ over $\mathbb{Z}_q$. -/
def evalPoly204 : List Fq204 → Fq204 → Fq204
  | [], _ => Fq204.zero
  | c :: cs, w => Fq204.add c (Fq204.mul w (evalPoly204 cs w))

theorem evalPoly204_append : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (xs ++ ys) w =
      Fq204.add (evalPoly204 xs w) (Fq204.mul (Fq204.pow w xs.length) (evalPoly204 ys w))
  | [], ys, w => by
    dsimp only [List.nil_append, evalPoly204, List.length_nil, Fq204.pow]
    rw [Fq204.zero_add, Fq204.one_mul]
  | c :: cs, ys, w => by
    simp only [List.cons_append, evalPoly204, evalPoly204_append cs ys w, List.length_cons,
      Fq204.pow, Fq204.left_distrib, Fq204.add_assoc]
    congr 2
    rw [← Fq204.mul_assoc, Fq204.mul_comm w (Fq204.pow w cs.length)]

def addPolyList : List Fq204 → List Fq204 → List Fq204
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => Fq204.add x y :: addPolyList xs ys

def subPolyList : List Fq204 → List Fq204 → List Fq204
  | [], [] => []
  | [], y :: ys => Fq204.neg y :: subPolyList [] ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => Fq204.sub x y :: subPolyList xs ys

def scalePolyList (k : Fq204) : List Fq204 → List Fq204
  | [] => []
  | x :: xs => Fq204.mul k x :: scalePolyList k xs

/-- Unreduced Cauchy product of two polynomials in $\mathbb{Z}_q[X]$. -/
def cauchyMulList : List Fq204 → List Fq204 → List Fq204
  | [], _ => []
  | a :: as, bs => addPolyList (scalePolyList a bs) (Fq204.zero :: cauchyMulList as bs)

theorem evalPoly204_addPolyList : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (addPolyList xs ys) w = Fq204.add (evalPoly204 xs w) (evalPoly204 ys w)
  | [], ys, w => by dsimp only [addPolyList, evalPoly204]; rw [Fq204.zero_add]
  | x :: xs, [], w => by dsimp only [addPolyList, evalPoly204]; rw [Fq204.add_zero]
  | x :: xs, y :: ys, w => by
    simp only [addPolyList, evalPoly204, evalPoly204_addPolyList xs ys w, Fq204.left_distrib]
    rw [Fq204.add_assoc x y,
        ← Fq204.add_assoc y (Fq204.mul w (evalPoly204 xs w)),
        Fq204.add_comm y (Fq204.mul w (evalPoly204 xs w)),
        Fq204.add_assoc (Fq204.mul w (evalPoly204 xs w)) y,
        ← Fq204.add_assoc x (Fq204.mul w (evalPoly204 xs w))]

theorem evalPoly204_subPolyList : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (subPolyList xs ys) w = Fq204.sub (evalPoly204 xs w) (evalPoly204 ys w)
  | [], [], _ => by dsimp only [subPolyList, evalPoly204]; rw [Fq204.sub_zero]
  | [], y :: ys, w => by
    simp only [subPolyList, evalPoly204, evalPoly204_subPolyList [] ys w]
    rw [Fq204.sub_eq_add_neg, Fq204.zero_add, Fq204.sub_eq_add_neg Fq204.zero,
        Fq204.zero_add, Fq204.mul_neg, Fq204.neg_add]
  | x :: xs, [], w => by dsimp only [subPolyList, evalPoly204]; rw [Fq204.sub_zero]
  | x :: xs, y :: ys, w => by
    simp only [subPolyList, evalPoly204, evalPoly204_subPolyList xs ys w,
      Fq204.sub_eq_add_neg, Fq204.left_distrib, Fq204.mul_neg, Fq204.neg_add]
    rw [Fq204.add_assoc x, ← Fq204.add_assoc (Fq204.neg y),
        Fq204.add_comm (Fq204.neg y) (Fq204.mul w _),
        Fq204.add_assoc (Fq204.mul w _), ← Fq204.add_assoc x]

theorem evalPoly204_scalePolyList (k : Fq204) : ∀ (xs : List Fq204) (w : Fq204),
    evalPoly204 (scalePolyList k xs) w = Fq204.mul k (evalPoly204 xs w)
  | [], _ => by dsimp only [scalePolyList, evalPoly204]; rw [Fq204.mul_zero]
  | x :: xs, w => by
    simp only [scalePolyList, evalPoly204, evalPoly204_scalePolyList k xs w, Fq204.left_distrib]
    congr 1
    rw [← Fq204.mul_assoc, Fq204.mul_comm w k, Fq204.mul_assoc]

theorem evalPoly204_cauchyMulList : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (cauchyMulList xs ys) w = Fq204.mul (evalPoly204 xs w) (evalPoly204 ys w)
  | [], ys, _ => by dsimp only [cauchyMulList, evalPoly204]; rw [Fq204.zero_mul]
  | a :: as, ys, w => by
    simp only [cauchyMulList, evalPoly204, evalPoly204_addPolyList, evalPoly204_scalePolyList,
      Fq204.zero_add, evalPoly204_cauchyMulList as ys w, Fq204.right_distrib, Fq204.mul_assoc]

private theorem length_addPolyList : ∀ (xs ys : List Fq204),
    (addPolyList xs ys).length = max xs.length ys.length
  | [], ys => by simp [addPolyList]
  | x :: xs, [] => by simp [addPolyList]
  | _ :: xs, _ :: ys => by simp [addPolyList, length_addPolyList xs ys, Nat.succ_max_succ]

private theorem length_subPolyList_left : ∀ (xs ys : List Fq204),
    ys.length ≤ xs.length → (subPolyList xs ys).length = xs.length
  | xs, [], _ => by cases xs <;> rfl
  | [], _ :: _, h => by simp at h
  | _ :: xs, _ :: ys, h => by
    simp only [List.length_cons] at h
    simp [subPolyList, length_subPolyList_left xs ys (by omega)]

private theorem length_scalePolyList (k : Fq204) : ∀ (xs : List Fq204),
    (scalePolyList k xs).length = xs.length
  | [] => rfl
  | _ :: xs => by simp [scalePolyList, length_scalePolyList k xs]

private theorem length_cauchyMulList : ∀ (xs ys : List Fq204),
    xs ≠ [] → ys ≠ [] → (cauchyMulList xs ys).length = xs.length + ys.length - 1
  | [], _, h, _ => False.elim (h rfl)
  | [a], ys, _, hys => by
    have hpos : 1 ≤ ys.length := by
      cases ys with
      | nil => exact False.elim (hys rfl)
      | cons _ _ => simp
    dsimp only [cauchyMulList]
    rw [length_addPolyList, length_scalePolyList]
    simp only [List.length_cons, List.length_nil]
    omega
  | a :: b :: as, ys, _, hys => by
    have hpos : 1 ≤ ys.length := by
      cases ys with
      | nil => exact False.elim (hys rfl)
      | cons _ _ => simp
    have ih := length_cauchyMulList (b :: as) ys (by simp) hys
    change (addPolyList (scalePolyList a ys) (Fq204.zero :: cauchyMulList (b :: as) ys)).length =
      (a :: b :: as).length + ys.length - 1
    rw [length_addPolyList, length_scalePolyList, List.length_cons, ih]
    simp only [List.length_cons]
    omega

/-- Coefficient-domain negacyclic multiplication in $\mathbb{Z}_q[X]/(X^{256} + 1)$ (`X^256 ≡ -1`). -/
def negacyclicMulList (xs ys : List Fq204) : List Fq204 :=
  let prod := cauchyMulList xs ys
  subPolyList (prod.take 256) (prod.drop 256)

/-- Coefficient-domain negacyclic multiplication on `Poly256`. -/
def negacyclicMul (a b : Poly256) : Poly256 :=
  PolyTree.ofList 8 (negacyclicMulList (PolyTree.toList a) (PolyTree.toList b))

theorem length_negacyclicMulList {xs ys : List Fq204}
    (hx : xs.length = 256) (hy : ys.length = 256) :
    (negacyclicMulList xs ys).length = 256 := by
  unfold negacyclicMulList
  have hxNe : xs ≠ [] := by intro h; rw [h] at hx; simp at hx
  have hyNe : ys ≠ [] := by intro h; rw [h] at hy; simp at hy
  have hlen : (cauchyMulList xs ys).length = 511 := by
    rw [length_cauchyMulList xs ys hxNe hyNe, hx, hy]
  have htake : ((cauchyMulList xs ys).take 256).length = 256 := by simp [hlen]
  have hdrop : ((cauchyMulList xs ys).drop 256).length = 255 := by simp [hlen]
  rw [length_subPolyList_left _ _ (by omega), htake]

/-- Evaluation at any root $\omega$ of $X^{256} + 1 = 0$ ($\omega^{256} = -1$) is a ring homomorphism. -/
theorem evalPoly204_negacyclicMulList {xs ys : List Fq204}
    (hx : xs.length = 256) (hy : ys.length = 256)
    {w : Fq204} (hw : Fq204.pow w 256 = Fq204.neg Fq204.one) :
    evalPoly204 (negacyclicMulList xs ys) w =
      Fq204.mul (evalPoly204 xs w) (evalPoly204 ys w) := by
  unfold negacyclicMulList
  have hxNe : xs ≠ [] := by intro h; rw [h] at hx; simp at hx
  have hyNe : ys ≠ [] := by intro h; rw [h] at hy; simp at hy
  have hlen : (cauchyMulList xs ys).length = 511 := by
    rw [length_cauchyMulList xs ys hxNe hyNe, hx, hy]
  let prod := cauchyMulList xs ys
  have hsplit : prod = prod.take 256 ++ prod.drop 256 := (List.take_append_drop 256 prod).symm
  have htakeLen : (prod.take 256).length = 256 := by dsimp [prod]; simp [hlen]
  have hevalProd : evalPoly204 prod w = Fq204.mul (evalPoly204 xs w) (evalPoly204 ys w) :=
    evalPoly204_cauchyMulList xs ys w
  rw [← hevalProd, hsplit, evalPoly204_append, htakeLen, hw, evalPoly204_subPolyList,
      Fq204.sub_eq_add_neg]
  congr 1
  rw [Fq204.mul_comm (Fq204.neg Fq204.one), Fq204.mul_neg, Fq204.mul_one]

/-! #### Connecting 8-Stage `nttStage` Leaves to `evalPoly204` at Roots of $X^{256} + 1$ -/

/-- Tree of evaluation roots generated by the FIPS 204 radix-2 twist `e ↦ (e/2, e/2 + 256)`. -/
def rootTree : (d : Nat) → Nat → PolyTree d
  | 0, e => .leaf (Fq204.pow mldsaZeta e)
  | d + 1, e => .branch (rootTree d (e / 2)) (rootTree d (e / 2 + 256))

/-- Map polynomial evaluation `evalPoly204 coeffs` across every root in a `PolyTree d`. -/
def evalAtTree (coeffs : List Fq204) : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf w => .leaf (evalPoly204 coeffs w)
  | _ + 1, .branch rL rR => .branch (evalAtTree coeffs rL) (evalAtTree coeffs rR)

private theorem addPolyList_append : ∀ {xs1 xs2 ys1 ys2 : List Fq204},
    xs1.length = ys1.length →
    addPolyList (xs1 ++ xs2) (ys1 ++ ys2) = addPolyList xs1 ys1 ++ addPolyList xs2 ys2
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => (Nat.succ_ne_zero _ h.symm).elim
  | _ :: _, _, [], _, h => (Nat.succ_ne_zero _ h).elim
  | _ :: xs1, xs2, _ :: ys1, ys2, h => by
    simp only [List.length_cons] at h
    simp [addPolyList, addPolyList_append (Nat.succ.inj h)]

private theorem subPolyList_append : ∀ {xs1 xs2 ys1 ys2 : List Fq204},
    xs1.length = ys1.length →
    subPolyList (xs1 ++ xs2) (ys1 ++ ys2) = subPolyList xs1 ys1 ++ subPolyList xs2 ys2
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => (Nat.succ_ne_zero _ h.symm).elim
  | _ :: _, _, [], _, h => (Nat.succ_ne_zero _ h).elim
  | _ :: xs1, xs2, _ :: ys1, ys2, h => by
    simp only [List.length_cons] at h
    simp [subPolyList, subPolyList_append (Nat.succ.inj h)]

private theorem scalePolyList_append (k : Fq204) : ∀ (xs1 xs2 : List Fq204),
    scalePolyList k (xs1 ++ xs2) = scalePolyList k xs1 ++ scalePolyList k xs2
  | [], _ => rfl
  | _ :: xs1, xs2 => by simp [scalePolyList, scalePolyList_append k xs1 xs2]

private theorem toList_addTree : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.toList (PolyTree.add a b) = addPolyList (PolyTree.toList a) (PolyTree.toList b)
  | 0, .leaf _, .leaf _ => rfl
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.add, PolyTree.toList, toList_addTree]
    exact (addPolyList_append (by rw [PolyTree.length_toList, PolyTree.length_toList])).symm

private theorem toList_subTree : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.toList (PolyTree.sub a b) = subPolyList (PolyTree.toList a) (PolyTree.toList b)
  | 0, .leaf _, .leaf _ => rfl
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.sub, PolyTree.toList, toList_subTree]
    exact (subPolyList_append (by rw [PolyTree.length_toList, PolyTree.length_toList])).symm

private theorem toList_scaleTree (k : Fq204) : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.toList (PolyTree.scale k a) = scalePolyList k (PolyTree.toList a)
  | 0, .leaf _ => rfl
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.scale, PolyTree.toList, toList_scaleTree k, scalePolyList_append]

private theorem allLeaves_imp {P Q : Fq204 → Prop} (hImp : ∀ x, P x → Q x) :
    ∀ {d : Nat} {r : PolyTree d}, PolyTree.AllLeaves P r → PolyTree.AllLeaves Q r
  | 0, .leaf _, h => hImp _ h
  | _ + 1, .branch _ _, h => ⟨allLeaves_imp hImp h.1, allLeaves_imp hImp h.2⟩

private theorem evalAtTree_congr {c1 c2 : List Fq204} {P : Fq204 → Prop}
    (hEq : ∀ w, P w → evalPoly204 c1 w = evalPoly204 c2 w) :
    ∀ {d : Nat} {r : PolyTree d}, PolyTree.AllLeaves P r → evalAtTree c1 r = evalAtTree c2 r
  | 0, .leaf w, hw => congrArg PolyTree.leaf (hEq w hw)
  | _ + 1, .branch _ _, h => by
    simp only [evalAtTree, evalAtTree_congr hEq h.1, evalAtTree_congr hEq h.2]

private theorem rootTree_allLeavesPow :
    ∀ (d e : Nat), 2 ^ d ∣ e → d ≤ 8 →
      PolyTree.AllLeaves (fun w => Fq204.pow w (2 ^ d) = Fq204.pow mldsaZeta e) (rootTree d e)
  | 0, e, _, _ => by
    dsimp only [rootTree, PolyTree.AllLeaves, Nat.pow_zero, Fq204.pow]
    rw [Fq204.one_mul]
  | d + 1, e, hdvd, hdle => by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : e = (2 ^ d * k) * 2 := by rw [hk, Nat.pow_succ, Nat.mul_right_comm]
    have heDiv : e / 2 = 2 ^ d * k := by rw [hk2]; exact Nat.mul_div_cancel _ (by decide)
    have hdvdL : 2 ^ d ∣ (e / 2) := ⟨k, heDiv⟩
    have hdvd256 : 2 ^ d ∣ 256 := by
      obtain ⟨t, ht⟩ : ∃ t, 8 = d + t := ⟨8 - d, by omega⟩
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ht, Nat.pow_add]
      exact Nat.dvd_mul_right (2 ^ d) (2 ^ t)
    have hdvdR : 2 ^ d ∣ (e / 2 + 256) := Nat.dvd_add hdvdL hdvd256
    have he2 : 2 * (e / 2) = e := by rw [heDiv, hk2, Nat.mul_comm]
    simp only [rootTree, PolyTree.AllLeaves]
    refine ⟨allLeaves_imp ?_ (rootTree_allLeavesPow d (e / 2) hdvdL (by omega)),
            allLeaves_imp ?_ (rootTree_allLeavesPow d (e / 2 + 256) hdvdR (by omega))⟩
    · intro w hw
      rw [Nat.pow_succ, Fq204.pow_mul, hw, ← Fq204.pow_mul, Nat.mul_comm _ 2, he2]
    · intro w hw
      rw [Nat.pow_succ, Fq204.pow_mul, hw, ← Fq204.pow_mul]
      have hmul : (e / 2 + 256) * 2 = e + 512 := by omega
      rw [hmul, Fq204.pow_add, mldsaZeta_pow512_eq_one, Fq204.mul_one]

private theorem nttStage_eq_evalAtTree :
    ∀ (d e : Nat), 2 ^ d ∣ e → d ≤ 8 →
      ∀ (p : PolyTree d), nttStage d e p = evalAtTree (PolyTree.toList p) (rootTree d e)
  | 0, _, _, _, .leaf x => by
    dsimp only [nttStage, rootTree, evalAtTree, PolyTree.toList, evalPoly204]
    rw [Fq204.mul_zero, Fq204.add_zero]
  | d + 1, e, hdvd, hdle, .branch lo hi => by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : e = (2 ^ d * k) * 2 := by rw [hk, Nat.pow_succ, Nat.mul_right_comm]
    have heDiv : e / 2 = 2 ^ d * k := by rw [hk2]; exact Nat.mul_div_cancel _ (by decide)
    have hdvdL : 2 ^ d ∣ (e / 2) := ⟨k, heDiv⟩
    have hdvd256 : 2 ^ d ∣ 256 := by
      obtain ⟨t, ht⟩ : ∃ t, 8 = d + t := ⟨8 - d, by omega⟩
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ht, Nat.pow_add]
      exact Nat.dvd_mul_right (2 ^ d) (2 ^ t)
    have hdvdR : 2 ^ d ∣ (e / 2 + 256) := Nat.dvd_add hdvdL hdvd256
    simp only [nttStage, rootTree, evalAtTree, PolyTree.toList,
      nttStage_eq_evalAtTree d (e / 2) hdvdL (by omega),
      nttStage_eq_evalAtTree d (e / 2 + 256) hdvdR (by omega)]
    congr 1
    · apply evalAtTree_congr _ (rootTree_allLeavesPow d (e / 2) hdvdL (by omega))
      intro w hw
      rw [toList_addTree, toList_scaleTree, evalPoly204_addPolyList, evalPoly204_scalePolyList,
          evalPoly204_append, PolyTree.length_toList, hw]
    · apply evalAtTree_congr _ (rootTree_allLeavesPow d (e / 2 + 256) hdvdR (by omega))
      intro w hw
      rw [toList_subTree, toList_scaleTree, evalPoly204_subPolyList, evalPoly204_scalePolyList,
          evalPoly204_append, PolyTree.length_toList, hw,
          Fq204.pow_add mldsaZeta (e / 2) 256, mldsaZeta_pow256_eq_neg_one,
          Fq204.sub_eq_add_neg]
      congr 1
      rw [Fq204.mul_neg (Fq204.pow mldsaZeta (e / 2)) Fq204.one, Fq204.mul_one,
          Fq204.mul_comm (Fq204.neg _) (evalPoly204 hi.toList w),
          Fq204.mul_neg (evalPoly204 hi.toList w), Fq204.mul_comm (evalPoly204 hi.toList w)]

private theorem evalAtTree_pointwiseMul {xs ys : List Fq204}
    (hx : xs.length = 256) (hy : ys.length = 256) :
    ∀ {d : Nat} {r : PolyTree d},
      PolyTree.AllLeaves (fun w => Fq204.pow w 256 = Fq204.neg Fq204.one) r →
      evalAtTree (negacyclicMulList xs ys) r =
        PolyTree.pointwiseMul (evalAtTree xs r) (evalAtTree ys r)
  | 0, .leaf _, hw => congrArg PolyTree.leaf (evalPoly204_negacyclicMulList hx hy hw)
  | _ + 1, .branch _ _, h => by
    simp only [evalAtTree, PolyTree.pointwiseMul,
      evalAtTree_pointwiseMul hx hy h.1, evalAtTree_pointwiseMul hx hy h.2]

/-- **`fips204Ntt_negacyclicMul` (NTT Convolution Homomorphism)**:
    Forward 256-point FIPS 204 NTT maps negacyclic polynomial multiplication in
    $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$ to coordinatewise multiplication in $\mathbb{Z}_q^{256}$. -/
theorem fips204Ntt_negacyclicMul (a b : Poly256) :
    fips204Ntt (negacyclicMul a b) =
      PolyTree.pointwiseMul (fips204Ntt a) (fips204Ntt b) := by
  unfold fips204Ntt negacyclicMul
  have hlenA : (PolyTree.toList a).length = 256 := PolyTree.length_toList a
  have hlenB : (PolyTree.toList b).length = 256 := PolyTree.length_toList b
  have hlenM : (negacyclicMulList (PolyTree.toList a) (PolyTree.toList b)).length = 256 :=
    length_negacyclicMulList hlenA hlenB
  rw [nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8),
      nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8),
      nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8),
      PolyTree.toList_ofList hlenM]
  have hRoots := rootTree_allLeavesPow 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8)
  rw [show (2 : Nat) ^ 8 = 256 from rfl, mldsaZeta_pow256_eq_neg_one] at hRoots
  exact evalAtTree_pointwiseMul hlenA hlenB hRoots

/-- **`fips204InvNtt_pointwiseMul`**: inverse NTT of coordinatewise product equals exact
    negacyclic polynomial multiplication in $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$. -/
theorem fips204InvNtt_pointwiseMul (a b : Poly256) :
    fips204InvNtt (PolyTree.pointwiseMul (fips204Ntt a) (fips204Ntt b)) = negacyclicMul a b := by
  rw [← fips204Ntt_negacyclicMul, fips204InvNtt_ntt]

/-! #### `LawfulCommRing Poly256` via Linearity & NTT Homomorphism -/

private theorem polyTree_scale_add (z : Fq204) : ∀ {d : Nat} (x y : PolyTree d),
    PolyTree.scale z (PolyTree.add x y) = PolyTree.add (PolyTree.scale z x) (PolyTree.scale z y)
  | 0, .leaf x, .leaf y => congrArg PolyTree.leaf (Fq204.left_distrib z x y)
  | _ + 1, .branch x0 x1, .branch y0 y1 => by
    simp only [PolyTree.add, PolyTree.scale, polyTree_scale_add z]

private theorem polyTree_add_add_comm : ∀ {d : Nat} (x0 y0 x1 y1 : PolyTree d),
    PolyTree.add (PolyTree.add x0 y0) (PolyTree.add x1 y1) =
      PolyTree.add (PolyTree.add x0 x1) (PolyTree.add y0 y1)
  | 0, .leaf x0, .leaf y0, .leaf x1, .leaf y1 => congrArg PolyTree.leaf <| by
    rw [Fq204.add_assoc x0, ← Fq204.add_assoc y0, Fq204.add_comm y0 x1,
        Fq204.add_assoc x1, ← Fq204.add_assoc x0]
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1, .branch d0 d1 => by
    simp only [PolyTree.add, polyTree_add_add_comm]

private theorem polyTree_sub_add_comm : ∀ {d : Nat} (x0 y0 x1 y1 : PolyTree d),
    PolyTree.sub (PolyTree.add x0 y0) (PolyTree.add x1 y1) =
      PolyTree.add (PolyTree.sub x0 x1) (PolyTree.sub y0 y1)
  | 0, .leaf x0, .leaf y0, .leaf x1, .leaf y1 => congrArg PolyTree.leaf <| by
    rw [Fq204.sub_eq_add_neg, Fq204.sub_eq_add_neg, Fq204.sub_eq_add_neg, Fq204.neg_add,
        Fq204.add_assoc x0, ← Fq204.add_assoc y0, Fq204.add_comm y0 (Fq204.neg x1),
        Fq204.add_assoc (Fq204.neg x1), ← Fq204.add_assoc x0]
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1, .branch d0 d1 => by
    simp only [PolyTree.add, PolyTree.sub, polyTree_sub_add_comm]

private theorem nttStage_add : ∀ (d e : Nat) (a b : PolyTree d),
    nttStage d e (PolyTree.add a b) = PolyTree.add (nttStage d e a) (nttStage d e b)
  | 0, _, .leaf _, .leaf _ => rfl
  | d + 1, e, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.add, nttStage, polyTree_scale_add, polyTree_add_add_comm,
      polyTree_sub_add_comm, nttStage_add d]

theorem fips204Ntt_add (a b : Poly256) :
    fips204Ntt (PolyTree.add a b) = PolyTree.add (fips204Ntt a) (fips204Ntt b) :=
  nttStage_add 8 256 a b

private theorem evalPoly204_toList_zero :
    ∀ (d : Nat) (w : Fq204), evalPoly204 (PolyTree.toList (PolyTree.zero d)) w = Fq204.zero
  | 0, _ => by dsimp only [PolyTree.zero, PolyTree.toList, evalPoly204]; rw [Fq204.mul_zero, Fq204.add_zero]
  | d + 1, w => by
    simp only [PolyTree.zero, PolyTree.toList, evalPoly204_append, evalPoly204_toList_zero d w,
      Fq204.mul_zero, Fq204.add_zero]

private theorem evalPoly204_toList_constUnit :
    ∀ (d : Nat) (w : Fq204), evalPoly204 (PolyTree.toList (PolyTree.constUnit d)) w = Fq204.one
  | 0, _ => by dsimp only [PolyTree.constUnit, PolyTree.toList, evalPoly204]; rw [Fq204.mul_zero, Fq204.add_zero]
  | d + 1, w => by
    simp only [PolyTree.constUnit, PolyTree.toList, evalPoly204_append,
      evalPoly204_toList_constUnit d w, evalPoly204_toList_zero d w,
      Fq204.mul_zero, Fq204.add_zero]

private theorem evalAtTree_eq_ones {coeffs : List Fq204}
    (h1 : ∀ w, evalPoly204 coeffs w = Fq204.one) :
    ∀ {d : Nat} (r : PolyTree d), evalAtTree coeffs r = PolyTree.ones d
  | 0, .leaf w => congrArg PolyTree.leaf (h1 w)
  | _ + 1, .branch r0 r1 => by
    simp only [evalAtTree, PolyTree.ones, evalAtTree_eq_ones h1 r0, evalAtTree_eq_ones h1 r1]

private theorem evalAtTree_eq_zero {coeffs : List Fq204}
    (h0 : ∀ w, evalPoly204 coeffs w = Fq204.zero) :
    ∀ {d : Nat} (r : PolyTree d), evalAtTree coeffs r = PolyTree.zero d
  | 0, .leaf w => congrArg PolyTree.leaf (h0 w)
  | _ + 1, .branch r0 r1 => by
    simp only [evalAtTree, PolyTree.zero, evalAtTree_eq_zero h0 r0, evalAtTree_eq_zero h0 r1]

theorem fips204Ntt_constUnit :
    fips204Ntt (PolyTree.constUnit 8) = PolyTree.ones 8 := by
  unfold fips204Ntt
  rw [nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8)]
  exact evalAtTree_eq_ones (evalPoly204_toList_constUnit 8) _

theorem fips204Ntt_zero :
    fips204Ntt (PolyTree.zero 8) = PolyTree.zero 8 := by
  unfold fips204Ntt
  rw [nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8)]
  exact evalAtTree_eq_zero (evalPoly204_toList_zero 8) _

theorem polyTree_add_assoc : ∀ {d : Nat} (a b c : PolyTree d),
    PolyTree.add (PolyTree.add a b) c = PolyTree.add a (PolyTree.add b c)
  | 0, .leaf a, .leaf b, .leaf c => congrArg PolyTree.leaf (Fq204.add_assoc a b c)
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1 => by
    simp only [PolyTree.add, polyTree_add_assoc a0 b0 c0, polyTree_add_assoc a1 b1 c1]

theorem polyTree_add_comm : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.add a b = PolyTree.add b a
  | 0, .leaf a, .leaf b => congrArg PolyTree.leaf (Fq204.add_comm a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.add, polyTree_add_comm a0 b0, polyTree_add_comm a1 b1]

theorem polyTree_zero_add : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.add (PolyTree.zero d) a = a
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.zero_add a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.zero, PolyTree.add, polyTree_zero_add a0, polyTree_zero_add a1]

theorem polyTree_add_zero : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.add a (PolyTree.zero d) = a
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.add_zero a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.zero, PolyTree.add, polyTree_add_zero a0, polyTree_add_zero a1]

theorem polyTree_add_left_neg : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.add (PolyTree.neg a) a = PolyTree.zero d
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.add_left_neg a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.neg, PolyTree.add, PolyTree.zero, polyTree_add_left_neg a0, polyTree_add_left_neg a1]

theorem polyTree_sub_eq_add_neg : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.sub a b = PolyTree.add a (PolyTree.neg b)
  | 0, .leaf a, .leaf b => congrArg PolyTree.leaf (Fq204.sub_eq_add_neg a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.sub, PolyTree.add, PolyTree.neg, polyTree_sub_eq_add_neg a0 b0, polyTree_sub_eq_add_neg a1 b1]

private theorem polyTree_zero_pmul : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.pointwiseMul (PolyTree.zero d) a = PolyTree.zero d
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.zero_mul a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.zero, PolyTree.pointwiseMul, polyTree_zero_pmul a0, polyTree_zero_pmul a1]

private theorem polyTree_pmul_assoc : ∀ {d : Nat} (a b c : PolyTree d),
    PolyTree.pointwiseMul (PolyTree.pointwiseMul a b) c = PolyTree.pointwiseMul a (PolyTree.pointwiseMul b c)
  | 0, .leaf a, .leaf b, .leaf c => congrArg PolyTree.leaf (Fq204.mul_assoc a b c)
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1 => by simp only [PolyTree.pointwiseMul, polyTree_pmul_assoc]

private theorem polyTree_pmul_comm : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.pointwiseMul a b = PolyTree.pointwiseMul b a
  | 0, .leaf a, .leaf b => congrArg PolyTree.leaf (Fq204.mul_comm a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => by simp only [PolyTree.pointwiseMul, polyTree_pmul_comm a0, polyTree_pmul_comm a1]

private theorem polyTree_ones_pmul : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.pointwiseMul (PolyTree.ones d) a = a
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.one_mul a)
  | _ + 1, .branch a0 a1 => by simp only [PolyTree.ones, PolyTree.pointwiseMul, polyTree_ones_pmul]

private theorem polyTree_pmul_left_distrib : ∀ {d : Nat} (a b c : PolyTree d),
    PolyTree.pointwiseMul a (PolyTree.add b c) =
      PolyTree.add (PolyTree.pointwiseMul a b) (PolyTree.pointwiseMul a c)
  | 0, .leaf a, .leaf b, .leaf c => congrArg PolyTree.leaf (Fq204.left_distrib a b c)
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1 => by
    simp only [PolyTree.pointwiseMul, PolyTree.add, polyTree_pmul_left_distrib]

private theorem fips204Ntt_injective {a b : Poly256} (h : fips204Ntt a = fips204Ntt b) : a = b := by
  have := congrArg fips204InvNtt h
  rwa [fips204InvNtt_ntt, fips204InvNtt_ntt] at this

theorem negacyclicMul_assoc (a b c : Poly256) :
    negacyclicMul (negacyclicMul a b) c = negacyclicMul a (negacyclicMul b c) :=
  fips204Ntt_injective <| by simp only [fips204Ntt_negacyclicMul, polyTree_pmul_assoc]

theorem negacyclicMul_comm (a b : Poly256) :
    negacyclicMul a b = negacyclicMul b a :=
  fips204Ntt_injective <| by rw [fips204Ntt_negacyclicMul, fips204Ntt_negacyclicMul, polyTree_pmul_comm]

theorem negacyclicMul_zero_left (a : Poly256) :
    negacyclicMul (PolyTree.zero 8) a = PolyTree.zero 8 :=
  fips204Ntt_injective <| by rw [fips204Ntt_negacyclicMul, fips204Ntt_zero, polyTree_zero_pmul]

theorem negacyclicMul_one_left (a : Poly256) :
    negacyclicMul (PolyTree.constUnit 8) a = a :=
  fips204Ntt_injective <| by rw [fips204Ntt_negacyclicMul, fips204Ntt_constUnit, polyTree_ones_pmul]

theorem negacyclicMul_one_right (a : Poly256) :
    negacyclicMul a (PolyTree.constUnit 8) = a := by
  rw [negacyclicMul_comm, negacyclicMul_one_left]

theorem negacyclicMul_left_distrib (a b c : Poly256) :
    negacyclicMul a (PolyTree.add b c) = PolyTree.add (negacyclicMul a b) (negacyclicMul a c) :=
  fips204Ntt_injective <| by
    rw [fips204Ntt_negacyclicMul, fips204Ntt_add, fips204Ntt_add,
        fips204Ntt_negacyclicMul, fips204Ntt_negacyclicMul, polyTree_pmul_left_distrib]

theorem negacyclicMul_right_distrib (a b c : Poly256) :
    negacyclicMul (PolyTree.add a b) c = PolyTree.add (negacyclicMul a c) (negacyclicMul b c) := by
  rw [negacyclicMul_comm, negacyclicMul_left_distrib, negacyclicMul_comm c a, negacyclicMul_comm c b]

theorem poly256_add_left_cancel {a b c : Poly256} (h : PolyTree.add a b = PolyTree.add a c) : b = c := by
  have h1 := congrArg (PolyTree.add (PolyTree.neg a)) h
  rwa [← polyTree_add_assoc, ← polyTree_add_assoc, polyTree_add_left_neg,
       polyTree_zero_add, polyTree_zero_add] at h1

instance : CommRingOps Poly256 where
  zero := PolyTree.zero 8
  one := PolyTree.constUnit 8
  add := PolyTree.add
  mul := negacyclicMul
  neg := PolyTree.neg
  sub := PolyTree.sub

instance : LawfulCommRing Poly256 where
  add_assoc := polyTree_add_assoc
  add_comm := polyTree_add_comm
  zero_add := polyTree_zero_add
  add_zero := polyTree_add_zero
  add_left_neg := polyTree_add_left_neg
  sub_eq_add_neg := polyTree_sub_eq_add_neg
  mul_assoc := negacyclicMul_assoc
  mul_comm := negacyclicMul_comm
  one_mul := negacyclicMul_one_left
  mul_one := negacyclicMul_one_right
  left_distrib := negacyclicMul_left_distrib
  right_distrib := negacyclicMul_right_distrib

/-! ### §1.4 Exact FIPS 204 `Power2Round`, `Decompose`, `MakeHint`, `UseHint` & `HighBits` Shift Lemma -/

/-- Exact NIST FIPS 204 `Power2Round(r)` (`Algorithm 35`, $d = 13$, $2^d = 8192$):
    returns `(r1, r0)` with `r0 ∈ (-4096, 4096]`. -/
@[expose] def power2Round (r : Fq204) : Nat × Int :=
  let low : Nat := r.val % 8192
  let r0 : Int := if 4096 < low then (low : Int) - 8192 else (low : Int)
  let r1 : Nat := ((r.val : Int) - r0).toNat / 8192
  (r1, r0)

/-- **`power2Round_reconstruct`**: for every $r \in \mathbb{Z}_q$, `power2Round r = (r1, r0)` satisfies
    $-2^{12} < r_0 \le 2^{12}$, $r_1 < 1024$, and exact integer reconstruction $r_1 \cdot 2^{13} + r_0 = r$. -/
theorem power2Round_reconstruct (r : Fq204) :
    -4096 < (power2Round r).2 ∧ (power2Round r).2 ≤ 4096 ∧ (power2Round r).1 < 1024 ∧
    (((power2Round r).1 : Int) * 8192 + (power2Round r).2 = (r.val : Int)) ∧
    Fq204.add (Fq204.mul (Fq204.ofNat (power2Round r).1) (Fq204.ofNat 8192))
              (Fq204.ofInt (power2Round r).2) = r := by
  have hr := r.isLt
  have hEqInt :
      -4096 < (power2Round r).2 ∧ (power2Round r).2 ≤ 4096 ∧
      (power2Round r).1 < 1024 ∧ (((power2Round r).1 : Int) * 8192 + (power2Round r).2 = (r.val : Int)) := by
    unfold power2Round
    unfold mldsaQ at hr
    dsimp only
    split <;> (refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)
  refine ⟨hEqInt.1, hEqInt.2.1, hEqInt.2.2.1, hEqInt.2.2.2, ?_⟩
  let r1 := (power2Round r).1
  let r0 := (power2Round r).2
  have hRec : (r1 : Int) * 8192 + r0 = (r.val : Int) := hEqInt.2.2.2
  have hmul : Fq204.mul (Fq204.ofNat r1) (Fq204.ofNat 8192) = Fq204.ofInt ((r1 : Int) * 8192) := by
    have hmulNat : Fq204.mul (Fq204.ofNat r1) (Fq204.ofNat 8192) = Fq204.ofNat (r1 * 8192) := by
      apply Fq204.ext
      simp only [Fq204.mul_val, Fq204.ofNat_val, Nat.mod_mul_mod, Nat.mul_mod_mod]
    rw [hmulNat]
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val, Fq204.ofNat_val, Int.natCast_emod, Int.natCast_mul]
    rfl
  change Fq204.add (Fq204.mul (Fq204.ofNat r1) (Fq204.ofNat 8192)) (Fq204.ofInt r0) = r
  rw [hmul, Fq204.ofInt_add, hRec, Fq204.ofInt_nat]

/-- Exact NIST FIPS 204 `Decompose(r)` (`Algorithm 36`) for `ML-DSA-44`
    ($\gamma_2 = 95232, \alpha = 2\gamma_2 = 190464, m = 44$). -/
@[expose] def decompose (r : Fq204) : Nat × Int :=
  let rem : Nat := r.val % 190464
  let r0p : Int := if 95232 < rem then (rem : Int) - 190464 else (rem : Int)
  if (r.val : Int) - r0p = 8380416 then
    (0, r0p - 1)
  else
    (((r.val : Int) - r0p).toNat / 190464, r0p)

/-- Division-free 48-bit shift/multiply `decompose_ct` from `fips204_ntt.rs`
    (`M48_88 = (1 << 48) / 190464 + 1 = 1477838210`). -/
def decomposeCtSpec (r : Nat) : Nat × Int :=
  let m48 : Nat := 1477838210
  let qQuot : Nat := (r * m48) / 281474976710656
  let rem : Nat := r - qQuot * 190464
  let gtG2 : Bool := decide (95232 < rem)
  let r0Base : Int := if gtG2 then (rem : Int) - 190464 else (rem : Int)
  if (r : Int) - r0Base = 8380416 then
    (0, r0Base - 1)
  else
    (qQuot + (if gtG2 then 1 else 0), r0Base)

/-- **`decomposeCt_eq_decompose`**: division-free `decompose_ct` equals exact FIPS 204 `decompose`
    over all $8{,}380{,}417$ field elements. -/
theorem decomposeCt_eq_decompose (r : Fq204) :
    decomposeCtSpec r.val = decompose r := by
  have hr := r.isLt
  unfold decomposeCtSpec decompose mldsaQ at *
  dsimp only
  have hq : (r.val * 1477838210) / 281474976710656 = r.val / 190464 := by omega
  have hrem : r.val - (r.val / 190464) * 190464 = r.val % 190464 := by omega
  rw [hq, hrem]
  if hgt : 95232 < r.val % 190464 then
    simp only [hgt, decide_true, ↓reduceIte]
    split
    · rfl
    · congr 1; omega
  else
    simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · congr 1; omega

/-- FIPS 204 `HighBits(r)` (`Algorithm 37`, returning `r1 ∈ [0, 44)`). -/
def mldsaHighBits (r : Fq204) : Nat := (decompose r).1

/-- FIPS 204 `LowBits(r)` (`Algorithm 38`, returning `r0 ∈ [-95232, 95232]`). -/
def mldsaLowBits (r : Fq204) : Int := (decompose r).2

/-- **`decompose_reconstruct`**: exact reconstruction $r \equiv r_1 \cdot 2\gamma_2 + r_0 \pmod q$
    and norm bounds $r_1 < 44$, $-\gamma_2 \le r_0 \le \gamma_2$. -/
theorem decompose_reconstruct (r : Fq204) :
    mldsaHighBits r < 44 ∧
    -95232 ≤ mldsaLowBits r ∧ mldsaLowBits r ≤ 95232 ∧
    (mldsaHighBits r ≠ 0 → -95232 < mldsaLowBits r) ∧
    Fq204.ofInt ((mldsaHighBits r : Int) * 190464 + mldsaLowBits r) = r := by
  have hr := r.isLt
  have hCore :
      mldsaHighBits r < 44 ∧
      -95232 ≤ mldsaLowBits r ∧ mldsaLowBits r ≤ 95232 ∧
      (mldsaHighBits r ≠ 0 → -95232 < mldsaLowBits r) ∧
      (((mldsaHighBits r : Int) * 190464 + mldsaLowBits r = (r.val : Int)) ∨
       ((mldsaHighBits r : Int) * 190464 + mldsaLowBits r = (r.val : Int) - 8380417)) := by
    unfold mldsaHighBits mldsaLowBits decompose
    unfold mldsaQ at hr
    dsimp only
    split <;> split <;> dsimp only <;> (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega)
  refine ⟨hCore.1, hCore.2.1, hCore.2.2.1, hCore.2.2.2.1, ?_⟩
  rcases hCore.2.2.2.2 with hExact | hWrap
  · rw [hExact, Fq204.ofInt_nat]
  · rw [hWrap]
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val]; unfold mldsaQ at hr ⊢
    rw [← Int.add_emod_right _ ((8380417 : Nat) : Int)]
    have hCancel : (r.val : Int) - 8380417 + ((8380417 : Nat) : Int) = (r.val : Int) := by omega
    rw [hCancel]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Interior uniqueness of `decompose`: any representation $u_1 \cdot 2\gamma_2 + u_0 \pmod q$
    with $u_1 < 44$ and $-95232 < u_0 \le 95232$ (or $u_1 = 0, u_0 = -95232$) uniquely determines
    `decompose = (u1, u0)`. -/
theorem decompose_ofInt_interior {u1 : Nat} {u0 : Int}
    (hu1 : u1 < 44) (hu0Lo : -95232 < u0 ∨ (u1 = 0 ∧ u0 = -95232)) (hu0Hi : u0 ≤ 95232) :
    decompose (Fq204.ofInt ((u1 : Int) * 190464 + u0)) = (u1, u0) := by
  if hCorner : (u1 = 0 ∧ u0 = -95232) ∨ (u1 = 0 ∧ u0 = -1) then
    rcases hCorner with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  else
    have hu0Strict : -95232 < u0 := by
      rcases hu0Lo with h | h
      · exact h
      · exact absurd (Or.inl h) hCorner
    clear hu0Lo
    have hv : ((Fq204.ofInt ((u1 : Int) * 190464 + u0)).val : Int) =
        ((u1 : Int) * 190464 + u0) % (8380417 : Int) := Fq204.ofInt_val _
    unfold decompose
    if hWrap : u1 = 0 ∧ u0 < 0 then
      rcases hWrap with ⟨hu1Zero, hu0Neg⟩
      subst hu1Zero
      have hu0NeM1 : u0 ≠ -1 := fun h => hCorner (Or.inr ⟨rfl, h⟩)
      clear hCorner
      have hu0LeMinus2 : u0 ≤ -2 := by omega
      simp only [Int.ofNat_zero, Int.zero_mul, Int.zero_add] at hv ⊢
      have hMod : u0 % (8380417 : Int) = 8380417 + u0 := by
        rw [← Int.add_emod_right u0 (8380417 : Int)]
        have hEq : u0 + (8380417 : Int) = 8380417 + u0 := by omega
        rw [hEq]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [hMod] at hv
      generalize (Fq204.ofInt u0).val = n at hv ⊢
      have hnDiv : n / 190464 = 43 := by omega
      have hgt : 95232 < n % 190464 := by omega
      have htop : (n : Int) - (((n % 190464 : Nat) : Int) - 190464) = 8380416 := by omega
      simp only [hgt, ↓reduceIte, htop]
      exact Prod.ext rfl (by omega)
    else
      have hNonneg : 0 ≤ (u1 : Int) * 190464 + u0 := by
        rcases Nat.eq_zero_or_pos u1 with h0 | hpos
        · have hu0nn : ¬ (u0 < 0) := fun h => hWrap ⟨h0, h⟩
          clear hWrap hCorner
          omega
        · clear hWrap hCorner
          omega
      clear hWrap hCorner
      have hMod : ((u1 : Int) * 190464 + u0) % (8380417 : Int) = (u1 : Int) * 190464 + u0 :=
        Int.emod_eq_of_lt hNonneg (by omega)
      rw [hMod] at hv
      generalize (Fq204.ofInt ((u1 : Int) * 190464 + u0)).val = n at hv ⊢
      dsimp only
      if hu0Pos : 0 ≤ u0 then
        have hngt : ¬ (95232 < n % 190464) := by omega
        have hntop : (n : Int) - ((n % 190464 : Nat) : Int) ≠ 8380416 := by omega
        simp only [hngt, ↓reduceIte, hntop]
        exact Prod.ext (by omega) (by omega)
      else
        have hgt : 95232 < n % 190464 := by omega
        have hntop : (n : Int) - (((n % 190464 : Nat) : Int) - 190464) ≠ 8380416 := by omega
        simp only [hgt, ↓reduceIte, hntop]
        exact Prod.ext (by omega) (by omega)

/-- **`centered_diff_lt_iff_lowBits_and_highBits`** (certifying `threshold_mldsa.rs` Phase 3):
    For any $r \in \mathbb{Z}_q$, $w_1 < 44$, and $B \le \gamma_2 = 95232$,
    $|(r - w_1 \cdot 2\gamma_2) \bmod^\pm q| < B$ holds if and only if
    $|\text{LowBits}(r)| < B \land \text{HighBits}(r) = w_1$. -/
theorem centered_diff_lt_iff_lowBits_and_highBits (r : Fq204) {w1 B : Nat}
    (hw1 : w1 < 44) (hB : B ≤ 95232) :
    Fq204.centeredAbs (Fq204.sub r (Fq204.ofNat (w1 * 190464))) < B ↔
      (mldsaLowBits r).natAbs < B ∧ mldsaHighBits r = w1 := by
  have hw1Int : Fq204.ofNat (w1 * 190464) = Fq204.ofInt ((w1 : Int) * 190464) := by
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val, Fq204.ofNat_val, Int.natCast_emod, Int.natCast_mul]
    rfl
  constructor
  · intro hAbs
    let diff := Fq204.sub r (Fq204.ofNat (w1 * 190464))
    let d := Fq204.toCenteredInt diff
    have hdAbs : d.natAbs < B := by dsimp [d]; rwa [Fq204.toCenteredInt_natAbs]
    have hrEq : r = Fq204.ofInt ((w1 : Int) * 190464 + d) := by
      calc r = Fq204.add (Fq204.ofNat (w1 * 190464)) diff := by
            dsimp [diff]
            rw [Fq204.sub_eq_add_neg, Fq204.add_comm _ (Fq204.add r _),
                Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
      _ = Fq204.add (Fq204.ofInt ((w1 : Int) * 190464)) (Fq204.ofInt d) := by
            rw [hw1Int, Fq204.ofInt_toCenteredInt]
      _ = Fq204.ofInt ((w1 : Int) * 190464 + d) := Fq204.ofInt_add _ _
    have hdec := decompose_ofInt_interior hw1 (u0 := d) (Or.inl (by omega)) (by omega)
    rw [← hrEq] at hdec
    have h1 : mldsaHighBits r = w1 := congrArg Prod.fst hdec
    have h2 : mldsaLowBits r = d := congrArg Prod.snd hdec
    rw [h2]; exact ⟨hdAbs, h1⟩
  · rintro ⟨hLow, hHigh⟩
    obtain ⟨_, _, _, _, hRec⟩ := decompose_reconstruct r
    have hSub : Fq204.sub r (Fq204.ofNat (w1 * 190464)) = Fq204.ofInt (mldsaLowBits r) := by
      conv => lhs; rw [← hRec, hHigh, hw1Int, Fq204.ofInt_sub]
      congr 1; omega
    rw [hSub, ← Fq204.toCenteredInt_natAbs,
        Fq204.toCenteredInt_ofInt_eq (by omega) (by omega)]
    exact hLow

/-- FIPS 204 Lemma 1 corollary: whenever $|\text{LowBits}(w - cs_2)| < \gamma_2 - \beta$ and
    $|cs_2 \bmod^\pm q| \le \beta$, $\text{HighBits}(w - cs_2) = \text{HighBits}(w)$. -/
theorem highBits_sub_eq_of_lowBits_lt (w cs2 : Fq204) {beta : Nat}
    (hBeta : beta ≤ 95232)
    (hLow : (mldsaLowBits (Fq204.sub w cs2)).natAbs < 95232 - beta)
    (hCs2 : Fq204.centeredAbs cs2 ≤ beta) :
    mldsaHighBits (Fq204.sub w cs2) = mldsaHighBits w := by
  let u := Fq204.sub w cs2
  change (mldsaLowBits u).natAbs < 95232 - beta at hLow
  obtain ⟨hu1Lt, _, _, -, huRec⟩ := decompose_reconstruct u
  let e := Fq204.toCenteredInt cs2
  have heAbs : e.natAbs ≤ beta := by dsimp [e]; rwa [Fq204.toCenteredInt_natAbs]
  have hu0Bounds : -((95232 - beta : Nat) : Int) < mldsaLowBits u ∧
      mldsaLowBits u < ((95232 - beta : Nat) : Int) := by constructor <;> omega
  have heBounds : -(beta : Int) ≤ e ∧ e ≤ (beta : Int) := by constructor <;> omega
  have hwEq : w = Fq204.ofInt ((mldsaHighBits u : Int) * 190464 + (mldsaLowBits u + e)) := by
    calc w = Fq204.add u cs2 := by
          dsimp [u]
          rw [Fq204.sub_eq_add_neg, Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
    _ = Fq204.add (Fq204.ofInt ((mldsaHighBits u : Int) * 190464 + mldsaLowBits u)) (Fq204.ofInt e) := by
          rw [huRec, Fq204.ofInt_toCenteredInt]
    _ = Fq204.ofInt ((mldsaHighBits u : Int) * 190464 + (mldsaLowBits u + e)) := by
          rw [Fq204.ofInt_add, Int.add_assoc]
  have hdecW := decompose_ofInt_interior hu1Lt (u0 := mldsaLowBits u + e) (Or.inl (by omega)) (by omega)
  rw [← hwEq] at hdecW
  exact (congrArg Prod.fst hdecW).symm

/-- Exact NIST FIPS 204 `MakeHint(z, r)` (`Algorithm 39`). -/
@[expose] def makeHint (z r : Fq204) : Bool :=
  decide (mldsaHighBits r ≠ mldsaHighBits (Fq204.add r z))

/-- Exact NIST FIPS 204 `UseHint(h, r)` (`Algorithm 40`, `ML-DSA-44` $m = 44$). -/
@[expose] def useHint (h : Bool) (r : Fq204) : Nat :=
  let (r1, r0) := decompose r
  if !h then r1
  else if 0 < r0 then
    if r1 + 1 = 44 then 0 else r1 + 1
  else
    if r1 = 0 then 43 else r1 - 1

/-- **Scalar FIPS 204 Supporting Hint Lemma (`useHint_makeHint_eq_highBits`)**:
    For every $u \in \mathbb{Z}_q$ with $|\text{LowBits}(u)| < \gamma_2$ and every $ct_0 \in \mathbb{Z}_q$
    with $|ct_0 \bmod^\pm q| < \gamma_2$,
    `useHint (makeHint (-ct0) (u + ct0)) (u + ct0) = mldsaHighBits u`. -/
theorem useHint_makeHint_eq_highBits (u ct0 : Fq204)
    (hLow : (mldsaLowBits u).natAbs < 95232)
    (hCt0 : Fq204.centeredAbs ct0 < 95232) :
    useHint (makeHint (Fq204.neg ct0) (Fq204.add u ct0)) (Fq204.add u ct0) = mldsaHighBits u := by
  have hCancel : Fq204.add (Fq204.add u ct0) (Fq204.neg ct0) = u := by
    rw [Fq204.add_assoc, Fq204.add_right_neg, Fq204.add_zero]
  unfold makeHint useHint
  rw [hCancel]
  obtain ⟨hu1Lt, _, _, -, huRec⟩ := decompose_reconstruct u
  let u1 := mldsaHighBits u
  let u0 := mldsaLowBits u
  let e := Fq204.toCenteredInt ct0
  have hu0Bounds : -95232 < u0 ∧ u0 < 95232 := by dsimp [u0]; constructor <;> omega
  have heAbs : e.natAbs < 95232 := by dsimp [e]; rwa [Fq204.toCenteredInt_natAbs]
  have heBounds : -95232 < e ∧ e < 95232 := by constructor <;> omega
  have hrEq : Fq204.add u ct0 = Fq204.ofInt ((u1 : Int) * 190464 + (u0 + e)) := by
    conv => lhs; rw [← huRec, ← Fq204.ofInt_toCenteredInt ct0]
    rw [Fq204.ofInt_add]; dsimp [u1, u0, e]; rw [Int.add_assoc]
  let s := u0 + e
  if hsMid : -95232 < s ∧ s ≤ 95232 then
    have hdecR : decompose (Fq204.add u ct0) = (u1, s) := by
      rw [hrEq]; exact decompose_ofInt_interior hu1Lt (Or.inl hsMid.1) hsMid.2
    have hr1 : mldsaHighBits (Fq204.add u ct0) = u1 := by unfold mldsaHighBits; rw [hdecR]
    change (let (r1, r0) := decompose (Fq204.add u ct0)
            if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
            else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
            else if r1 = 0 then 43 else r1 - 1) = u1
    rw [hdecR, hr1]
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.not_false, ↓reduceIte]
  else if hsHi : 95232 < s then
    clear hsMid
    let w0 := s - 190464
    have hw0Bounds : -95232 < w0 ∧ w0 < 0 := by dsimp [w0, s] at *; constructor <;> omega
    if hu1Top : u1 + 1 = 44 then
      have hu1Val : u1 = 43 := by omega
      have hrEqWrap : Fq204.add u ct0 = Fq204.ofInt (((0 : Nat) : Int) * 190464 + (w0 - 1)) := by
        rw [hrEq]; apply Fq204.ext; apply Int.ofNat_inj.mp
        rw [Fq204.ofInt_val, Fq204.ofInt_val]; unfold mldsaQ
        have hDiff : (u1 : Int) * 190464 + (u0 + e) =
            (((0 : Nat) : Int) * 190464 + (w0 - 1)) + ((8380417 : Nat) : Int) := by
          dsimp [w0, s] at *; omega
        rw [hDiff, Int.add_emod_right]
      have hdecR : decompose (Fq204.add u ct0) = (0, w0 - 1) := by
        rw [hrEqWrap]
        exact decompose_ofInt_interior (u1 := 0) (u0 := w0 - 1) (by omega)
          (by
            if hInt : -95232 < w0 - 1 then exact Or.inl hInt
            else exact Or.inr ⟨rfl, by omega⟩)
          (by omega)
      have hr1 : mldsaHighBits (Fq204.add u ct0) = 0 := by unfold mldsaHighBits; rw [hdecR]
      have hne : (0 : Nat) ≠ u1 := by omega
      have hnPos : ¬ (0 < w0 - 1) := by omega
      change (let (r1, r0) := decompose (Fq204.add u ct0)
              if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
              else if r1 = 0 then 43 else r1 - 1) = u1
      rw [hdecR, hr1, decide_eq_true hne]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnPos]
      omega
    else
      have hrEqCarry : Fq204.add u ct0 = Fq204.ofInt (((u1 + 1 : Nat) : Int) * 190464 + w0) := by
        rw [hrEq]; apply congrArg Fq204.ofInt; dsimp [w0, s]; omega
      have hdecR : decompose (Fq204.add u ct0) = (u1 + 1, w0) := by
        rw [hrEqCarry]
        exact decompose_ofInt_interior (u1 := u1 + 1) (u0 := w0) (by omega) (Or.inl hw0Bounds.1) (by omega)
      have hr1 : mldsaHighBits (Fq204.add u ct0) = u1 + 1 := by unfold mldsaHighBits; rw [hdecR]
      have hne : u1 + 1 ≠ u1 := by omega
      have hnPos : ¬ (0 < w0) := by omega
      have hnz : u1 + 1 ≠ 0 := by omega
      change (let (r1, r0) := decompose (Fq204.add u ct0)
              if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
              else if r1 = 0 then 43 else r1 - 1) = u1
      rw [hdecR, hr1, decide_eq_true hne]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnPos, hnz]
      omega
  else
    have hsLe : s ≤ -95232 :=
      Int.not_lt.mp (fun h => hsMid ⟨h, Int.not_lt.mp hsHi⟩)
    clear hsMid
    if hsExactZero : u1 = 0 ∧ s = -95232 then
      rcases hsExactZero with ⟨hu1Zero, hsEq⟩
      have hSumEq : u0 + e = -95232 := hsEq
      have hdecR : decompose (Fq204.add u ct0) = (0, -95232) := by
        rw [hrEq, hu1Zero, hSumEq]; decide
      have hr1 : mldsaHighBits (Fq204.add u ct0) = 0 := by unfold mldsaHighBits; rw [hdecR]
      change (let (r1, r0) := decompose (Fq204.add u ct0)
              if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
              else if r1 = 0 then 43 else r1 - 1) = u1
      rw [hdecR, hr1, hu1Zero]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.not_false, ↓reduceIte]
    else
      let w0 := s + 190464
      if hu1Zero : u1 = 0 then
        have hsNe : s ≠ -95232 := fun h => hsExactZero ⟨hu1Zero, h⟩
        clear hsExactZero
        have hsLt : s < -95232 := by omega
        have hw0Bounds : 0 < w0 ∧ w0 < 95232 := by dsimp [w0, s] at *; constructor <;> omega
        have hrEqBorrow : Fq204.add u ct0 = Fq204.ofInt (((43 : Nat) : Int) * 190464 + (w0 + 1)) := by
          rw [hrEq]; apply Fq204.ext; apply Int.ofNat_inj.mp
          rw [Fq204.ofInt_val, Fq204.ofInt_val]; unfold mldsaQ
          have hDiff : ((u1 : Int) * 190464 + (u0 + e)) + ((8380417 : Nat) : Int) =
              ((43 : Nat) : Int) * 190464 + (w0 + 1) := by
            dsimp [w0, s] at *; omega
          rw [← Int.add_emod_right ((u1 : Int) * 190464 + (u0 + e)) ((8380417 : Nat) : Int), hDiff]
        have hdecR : decompose (Fq204.add u ct0) = (43, w0 + 1) := by
          rw [hrEqBorrow]
          exact decompose_ofInt_interior (u1 := 43) (u0 := w0 + 1) (by omega) (Or.inl (by omega)) (by omega)
        have hr1 : mldsaHighBits (Fq204.add u ct0) = 43 := by unfold mldsaHighBits; rw [hdecR]
        have hne : (43 : Nat) ≠ u1 := by omega
        have hPos : 0 < w0 + 1 := by omega
        change (let (r1, r0) := decompose (Fq204.add u ct0)
                if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
                else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
                else if r1 = 0 then 43 else r1 - 1) = u1
        rw [hdecR, hr1, decide_eq_true hne]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPos]
        omega
      else
        clear hsExactZero
        have hw0Bounds : 0 < w0 ∧ w0 ≤ 95232 := by dsimp [w0, s] at *; constructor <;> omega
        have hrEqBorrow : Fq204.add u ct0 = Fq204.ofInt (((u1 - 1 : Nat) : Int) * 190464 + w0) := by
          rw [hrEq]; apply congrArg Fq204.ofInt; dsimp [w0, s]; omega
        have hdecR : decompose (Fq204.add u ct0) = (u1 - 1, w0) := by
          rw [hrEqBorrow]
          exact decompose_ofInt_interior (u1 := u1 - 1) (u0 := w0) (by omega) (Or.inl (by omega)) (by omega)
        have hr1 : mldsaHighBits (Fq204.add u ct0) = u1 - 1 := by unfold mldsaHighBits; rw [hdecR]
        have hne : u1 - 1 ≠ u1 := by omega
        have hPos : 0 < w0 := by omega
        have hnTop : (u1 - 1) + 1 ≠ 44 := by omega
        change (let (r1, r0) := decompose (Fq204.add u ct0)
                if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
                else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
                else if r1 = 0 then 43 else r1 - 1) = u1
        rw [hdecR, hr1, decide_eq_true hne]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPos, hnTop]
        omega

/-- **`#tooth` (`tooth_useHint_fails_when_ct0_ge_gamma2`)**:
    Dropping the `< γ_2` norm bound on `c * t0` breaks `UseHint` recovery even when
    `‖LowBits(u)‖_∞ < γ_2 - β` (`95000 < 95154`). -/
theorem tooth_useHint_fails_when_ct0_ge_gamma2 :
    let u : Fq204 := ⟨95000, by decide⟩
    let ct0 : Fq204 := ⟨95465, by decide⟩
    (mldsaLowBits u).natAbs < mldsa44Gamma2 - mldsa44Beta ∧
    mldsa44Gamma2 < Fq204.centeredAbs ct0 ∧
    useHint (makeHint (Fq204.neg ct0) (Fq204.add u ct0)) (Fq204.add u ct0) ≠ mldsaHighBits u := by
  decide

/-! #### Module-Lattice Lifting ($R_q^4$ & $R_q^{4 \times 4}$) & `highBits_az_sub_ct_eq_w1` -/

/-- `ML-DSA-44` length-4 module vector over $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$. -/
abbrev PolyVec4 := Fin 4 → Poly256

/-- `ML-DSA-44` $4 \times 4$ public matrix over $R_q$. -/
abbrev PolyMat4 := Fin 4 → Fin 4 → Poly256

def addVec4 (u v : PolyVec4) : PolyVec4 := fun i => PolyTree.add (u i) (v i)
def subVec4 (u v : PolyVec4) : PolyVec4 := fun i => PolyTree.sub (u i) (v i)
def negVec4 (u : PolyVec4) : PolyVec4 := fun i => PolyTree.neg (u i)
def mulPolyVec4 (c : Poly256) (v : PolyVec4) : PolyVec4 := fun i => negacyclicMul c (v i)

def matVecMul4 (A : PolyMat4) (v : PolyVec4) : PolyVec4 := fun i =>
  PolyTree.add
    (PolyTree.add (negacyclicMul (A i ⟨0, by decide⟩) (v ⟨0, by decide⟩))
                  (negacyclicMul (A i ⟨1, by decide⟩) (v ⟨1, by decide⟩)))
    (PolyTree.add (negacyclicMul (A i ⟨2, by decide⟩) (v ⟨2, by decide⟩))
                  (negacyclicMul (A i ⟨3, by decide⟩) (v ⟨3, by decide⟩)))

theorem matVecMul4_add (A : PolyMat4) (u v : PolyVec4) :
    matVecMul4 A (addVec4 u v) = addVec4 (matVecMul4 A u) (matVecMul4 A v) := by
  funext i
  dsimp only [matVecMul4, addVec4]
  rw [negacyclicMul_left_distrib, negacyclicMul_left_distrib,
      negacyclicMul_left_distrib, negacyclicMul_left_distrib,
      polyTree_add_add_comm (negacyclicMul _ (u ⟨0, _⟩)),
      polyTree_add_add_comm (negacyclicMul _ (u ⟨2, _⟩)),
      polyTree_add_add_comm (PolyTree.add _ _)]

theorem matVecMul4_mulPoly (A : PolyMat4) (c : Poly256) (v : PolyVec4) :
    matVecMul4 A (mulPolyVec4 c v) = mulPolyVec4 c (matVecMul4 A v) := by
  funext i
  dsimp only [matVecMul4, mulPolyVec4]
  have hSwapMul : ∀ x y z : Poly256, negacyclicMul x (negacyclicMul y z) =
      negacyclicMul y (negacyclicMul x z) := fun x y z => by
    rw [← negacyclicMul_assoc, negacyclicMul_comm x y, negacyclicMul_assoc]
  simp only [negacyclicMul_left_distrib, hSwapMul (A i _) c]

/-- Inductive tree of natural-number `HighBits` values ($2^d$ integers in $[0, 44)$). -/
inductive NatTree : Nat → Type where
  | leaf (n : Nat) : NatTree 0
  | branch {d : Nat} (lo hi : NatTree d) : NatTree (d + 1)
  deriving DecidableEq, Repr

/-- Inductive tree of boolean hint flags ($2^d$ bits). -/
inductive HintTree : Nat → Type where
  | leaf (b : Bool) : HintTree 0
  | branch {d : Nat} (lo hi : HintTree d) : HintTree (d + 1)
  deriving DecidableEq, Repr

def HintTree.weight : {d : Nat} → HintTree d → Nat
  | 0, .leaf b => if b then 1 else 0
  | _ + 1, .branch h0 h1 => weight h0 + weight h1

def power2RoundHighTree : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf r => .leaf (Fq204.ofNat ((power2Round r).1 * 8192))
  | _ + 1, .branch lo hi => .branch (power2RoundHighTree lo) (power2RoundHighTree hi)

def power2RoundLowTree : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf r => .leaf (Fq204.ofInt (power2Round r).2)
  | _ + 1, .branch lo hi => .branch (power2RoundLowTree lo) (power2RoundLowTree hi)

theorem power2RoundTree_reconstruct : ∀ {d : Nat} (p : PolyTree d),
    PolyTree.add (power2RoundHighTree p) (power2RoundLowTree p) = p
  | 0, .leaf r => congrArg PolyTree.leaf <| by
    have hmul : Fq204.ofNat ((power2Round r).1 * 8192) =
        Fq204.mul (Fq204.ofNat (power2Round r).1) (Fq204.ofNat 8192) := by
      apply Fq204.ext; simp [Fq204.ofNat_val, Fq204.mul_val, Nat.mul_mod]
    rw [hmul]
    exact (power2Round_reconstruct r).2.2.2.2
  | _ + 1, .branch lo hi => by
    simp only [power2RoundHighTree, power2RoundLowTree, PolyTree.add, power2RoundTree_reconstruct]

def highBitsTree : {d : Nat} → PolyTree d → NatTree d
  | 0, .leaf r => .leaf (mldsaHighBits r)
  | _ + 1, .branch lo hi => .branch (highBitsTree lo) (highBitsTree hi)

def lowBitsNormTree : {d : Nat} → PolyTree d → Nat
  | 0, .leaf r => (mldsaLowBits r).natAbs
  | _ + 1, .branch lo hi => max (lowBitsNormTree lo) (lowBitsNormTree hi)

def makeHintTree : {d : Nat} → PolyTree d → PolyTree d → HintTree d
  | 0, .leaf z, .leaf r => .leaf (makeHint z r)
  | _ + 1, .branch z0 z1, .branch r0 r1 => .branch (makeHintTree z0 r0) (makeHintTree z1 r1)

def useHintTree : {d : Nat} → HintTree d → PolyTree d → NatTree d
  | 0, .leaf h, .leaf r => .leaf (useHint h r)
  | _ + 1, .branch h0 h1, .branch r0 r1 => .branch (useHintTree h0 r0) (useHintTree h1 r1)

theorem useHintTree_makeHintTree : ∀ {d : Nat} (u ct0 : PolyTree d),
    lowBitsNormTree u < 95232 →
    PolyTree.infNorm ct0 < 95232 →
    useHintTree (makeHintTree (PolyTree.neg ct0) (PolyTree.add u ct0)) (PolyTree.add u ct0) =
      highBitsTree u
  | 0, .leaf u, .leaf ct0, hLow, hCt0 =>
    congrArg NatTree.leaf (useHint_makeHint_eq_highBits u ct0 hLow hCt0)
  | _ + 1, .branch u0 u1, .branch c0 c1, hLow, hCt0 => by
    simp only [lowBitsNormTree, PolyTree.infNorm] at hLow hCt0
    simp only [PolyTree.neg, PolyTree.add, makeHintTree, useHintTree, highBitsTree,
      useHintTree_makeHintTree u0 c0 (by omega) (by omega),
      useHintTree_makeHintTree u1 c1 (by omega) (by omega)]

theorem highBitsTree_sub_eq_of_lowBits_lt : ∀ {d : Nat} (w cs2 : PolyTree d) {beta : Nat},
    beta ≤ 95232 →
    lowBitsNormTree (PolyTree.sub w cs2) < 95232 - beta →
    PolyTree.infNorm cs2 ≤ beta →
    highBitsTree (PolyTree.sub w cs2) = highBitsTree w
  | 0, .leaf w, .leaf cs2, _, hB, hLow, hCs2 =>
    congrArg NatTree.leaf (highBits_sub_eq_of_lowBits_lt w cs2 hB hLow hCs2)
  | _ + 1, .branch w0 w1, .branch c0 c1, _, hB, hLow, hCs2 => by
    simp only [PolyTree.sub, lowBitsNormTree, PolyTree.infNorm] at hLow hCs2
    simp only [PolyTree.sub, highBitsTree,
      highBitsTree_sub_eq_of_lowBits_lt w0 c0 hB (by omega) (by omega),
      highBitsTree_sub_eq_of_lowBits_lt w1 c1 hB (by omega) (by omega)]

def power2RoundHighVec4 (t : PolyVec4) : PolyVec4 := fun i => power2RoundHighTree (t i)
def power2RoundLowVec4 (t : PolyVec4) : PolyVec4 := fun i => power2RoundLowTree (t i)
def highBitsVec4 (v : PolyVec4) : Fin 4 → NatTree 8 := fun i => highBitsTree (v i)
def makeHintVec4 (z r : PolyVec4) : Fin 4 → HintTree 8 := fun i => makeHintTree (z i) (r i)
def useHintVec4 (h : Fin 4 → HintTree 8) (r : PolyVec4) : Fin 4 → NatTree 8 :=
  fun i => useHintTree (h i) (r i)

def infNormVec4 (v : PolyVec4) : Nat :=
  max (max (PolyTree.infNorm (v ⟨0, by decide⟩)) (PolyTree.infNorm (v ⟨1, by decide⟩)))
      (max (PolyTree.infNorm (v ⟨2, by decide⟩)) (PolyTree.infNorm (v ⟨3, by decide⟩)))

def lowBitsNormVec4 (v : PolyVec4) : Nat :=
  max (max (lowBitsNormTree (v ⟨0, by decide⟩)) (lowBitsNormTree (v ⟨1, by decide⟩)))
      (max (lowBitsNormTree (v ⟨2, by decide⟩)) (lowBitsNormTree (v ⟨3, by decide⟩)))

def hintWeightVec4 (h : Fin 4 → HintTree 8) : Nat :=
  HintTree.weight (h ⟨0, by decide⟩) + HintTree.weight (h ⟨1, by decide⟩) +
  HintTree.weight (h ⟨2, by decide⟩) + HintTree.weight (h ⟨3, by decide⟩)

/-- **Module-Lattice Verification Identity (`az_sub_ct1_eq_w_sub_cs2_add_ct0`)**:
    Over $R_q^4$, whenever $z = y + c \cdot s_1$, $w = A \cdot y$, and $t = A \cdot s_1 + s_2 = t_1 \cdot 2^d + t_0$,
    $A \cdot z - c \cdot (t_1 \cdot 2^d) = (w - c \cdot s_2) + c \cdot t_0$ identically. -/
theorem az_sub_ct1_eq_w_sub_cs2_add_ct0
    (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256) :
    let t := addVec4 (matVecMul4 A s1) s2
    let t1Scaled := power2RoundHighVec4 t
    let t0 := power2RoundLowVec4 t
    let w := matVecMul4 A y
    let z := addVec4 y (mulPolyVec4 c s1)
    subVec4 (matVecMul4 A z) (mulPolyVec4 c t1Scaled) =
      addVec4 (subVec4 w (mulPolyVec4 c s2)) (mulPolyVec4 c t0) := by
  intro t t1Scaled t0 w z
  have htSplit : addVec4 t1Scaled t0 = t := by
    funext i; exact power2RoundTree_reconstruct (t i)
  have hAz : matVecMul4 A z = addVec4 w (mulPolyVec4 c (matVecMul4 A s1)) := by
    dsimp [z, w]; rw [matVecMul4_add, matVecMul4_mulPoly]
  rw [hAz]
  funext i
  have htRow : PolyTree.add (t1Scaled i) (t0 i) = PolyTree.add (matVecMul4 A s1 i) (s2 i) :=
    congrFun htSplit i
  dsimp only [addVec4, subVec4, mulPolyVec4]
  apply poly256_add_left_cancel (a := negacyclicMul c (t1Scaled i))
  have hSubCancel : ∀ x y : Poly256, PolyTree.add y (PolyTree.sub x y) = x := fun x y => by
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm y, polyTree_add_assoc,
        polyTree_add_left_neg, polyTree_add_zero]
  rw [hSubCancel]
  have hRhs :
      PolyTree.add (negacyclicMul c (t1Scaled i))
        (PolyTree.add (PolyTree.sub (w i) (negacyclicMul c (s2 i))) (negacyclicMul c (t0 i))) =
      PolyTree.add (PolyTree.sub (w i) (negacyclicMul c (s2 i)))
        (negacyclicMul c (PolyTree.add (t1Scaled i) (t0 i))) := by
    rw [negacyclicMul_left_distrib, polyTree_add_comm (negacyclicMul c (t1Scaled i)),
        polyTree_add_assoc, polyTree_add_comm (negacyclicMul c (t0 i))]
  rw [hRhs, htRow, negacyclicMul_left_distrib,
      polyTree_add_comm (negacyclicMul c (matVecMul4 A s1 i)) (negacyclicMul c (s2 i)),
      ← polyTree_add_assoc, polyTree_add_comm (PolyTree.sub (w i) _), hSubCancel]

/-- **Flagship §1 Theorem — Exact `HighBits` Shift Lemma (`highBits_az_sub_ct_eq_w1`)**:
    Over $R_q = \mathbb{Z}_{8380417}[X]/(X^{256} + 1)$ (`ML-DSA-44`, $k = \ell = 4$), whenever
    $z = y + c \cdot s_1$, $w = A \cdot y$, $t = A \cdot s_1 + s_2$,
    $\|\text{LowBits}(w - c \cdot s_2)\|_\infty < \gamma_2 - \beta$, and $\|c \cdot t_0\|_\infty < \gamma_2$,
    `UseHint(MakeHint(-c*t0, w - c*s2 + c*t0), A*z - c*t1*2^d) = HighBits(w - c*s2)`. -/
theorem highBits_az_sub_ct_eq_w1
    (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256) (beta : Nat)
    (hLow : lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2)) < mldsa44Gamma2 - beta)
    (hCt0 : infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 A s1) s2))) < mldsa44Gamma2) :
    let t := addVec4 (matVecMul4 A s1) s2
    let t1Scaled := power2RoundHighVec4 t
    let t0 := power2RoundLowVec4 t
    let w := matVecMul4 A y
    let z := addVec4 y (mulPolyVec4 c s1)
    let u := subVec4 w (mulPolyVec4 c s2)
    let ct0 := mulPolyVec4 c t0
    useHintVec4 (makeHintVec4 (negVec4 ct0) (addVec4 u ct0))
                (subVec4 (matVecMul4 A z) (mulPolyVec4 c t1Scaled)) =
      highBitsVec4 u := by
  intro t t1Scaled t0 w z u ct0
  have hId := az_sub_ct1_eq_w_sub_cs2_add_ct0 A s1 s2 y c
  dsimp only at hId
  rw [hId]
  funext i
  have hFinCases : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    rcases i with ⟨idx, hidx⟩
    have hIdx : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hIdx with rfl | rfl | rfl | rfl <;> simp
  rcases hFinCases with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [useHintVec4, makeHintVec4, highBitsVec4, negVec4, addVec4, u, ct0, w, t0, t]
    unfold lowBitsNormVec4 mldsa44Gamma2 at hLow
    unfold infNormVec4 mldsa44Gamma2 at hCt0
    exact useHintTree_makeHintTree _ _ (by omega) (by omega)

def idMat4 : PolyMat4 :=
  fun i j => if i = j then PolyTree.constUnit 8 else PolyTree.zero 8

private theorem matVecMul4_idMat4 (v : PolyVec4) : matVecMul4 idMat4 v = v := by
  funext i
  have hFinCases : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    rcases i with ⟨idx, hidx⟩
    have hIdx : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hIdx with rfl | rfl | rfl | rfl <;> simp
  rcases hFinCases with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [matVecMul4, idMat4]
    simp only [↓reduceIte, Fin.mk.injEq, Nat.reduceEqDiff,
      negacyclicMul_one_left, negacyclicMul_zero_left,
      polyTree_add_zero, polyTree_zero_add]

/-- Cyclic coordinate shift: row `i` selects coordinate `i + 1`. Not the identity. -/
def shiftMat4 : PolyMat4 :=
  fun i j => if (i.val + 1) % 4 = j.val then PolyTree.constUnit 8 else PolyTree.zero 8

private theorem matVecMul4_shiftMat4_const (p : Poly256) :
    matVecMul4 shiftMat4 (fun _ => p) = fun _ => p := by
  funext i
  have hFinCases : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    rcases i with ⟨idx, hidx⟩
    have hIdx : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hIdx with rfl | rfl | rfl | rfl <;> simp
  rcases hFinCases with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [matVecMul4, shiftMat4]
    simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff,
      negacyclicMul_one_left, negacyclicMul_zero_left,
      polyTree_add_zero, polyTree_zero_add]

theorem shiftMat4_ne_idMat4 : shiftMat4 ≠ idMat4 := by
  intro h
  have h00 := congrFun (congrFun h ⟨0, by decide⟩) ⟨0, by decide⟩
  simp only [shiftMat4, idMat4, ↓reduceIte, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff] at h00
  exact absurd h00 (by decide)

def polyTreeConstLeaf : (d : Nat) → Fq204 → PolyTree d
  | 0, x => .leaf x
  | d + 1, x => .branch (polyTreeConstLeaf d x) (polyTreeConstLeaf d x)

private theorem polyTreeConstLeaf_zero_eq : ∀ (d : Nat), polyTreeConstLeaf d Fq204.zero = PolyTree.zero d
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.zero, polyTreeConstLeaf_zero_eq d]

private theorem polyTreeConstLeaf_add (a b : Fq204) : ∀ (d : Nat),
    PolyTree.add (polyTreeConstLeaf d a) (polyTreeConstLeaf d b) = polyTreeConstLeaf d (Fq204.add a b)
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.add, polyTreeConstLeaf_add a b d]

private theorem polyTreeConstLeaf_neg (a : Fq204) : ∀ (d : Nat),
    PolyTree.neg (polyTreeConstLeaf d a) = polyTreeConstLeaf d (Fq204.neg a)
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.neg, polyTreeConstLeaf_neg a d]

private theorem polyTreeConstLeaf_infNorm (a : Fq204) : ∀ (d : Nat),
    PolyTree.infNorm (polyTreeConstLeaf d a) = Fq204.centeredAbs a
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.infNorm, polyTreeConstLeaf_infNorm a d, Nat.max_self]

private theorem polyTreeConstLeaf_lowBitsNorm (a : Fq204) : ∀ (d : Nat),
    lowBitsNormTree (polyTreeConstLeaf d a) = (mldsaLowBits a).natAbs
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, lowBitsNormTree, polyTreeConstLeaf_lowBitsNorm a d, Nat.max_self]

private theorem polyTreeConstLeaf_power2RoundLow (a : Fq204) : ∀ (d : Nat),
    power2RoundLowTree (polyTreeConstLeaf d a) = polyTreeConstLeaf d (Fq204.ofInt (power2Round a).2)
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, power2RoundLowTree, polyTreeConstLeaf_power2RoundLow a d]

private theorem polyTreeConstLeaf_hintWeight (z r : Fq204) : ∀ (d : Nat),
    HintTree.weight (makeHintTree (polyTreeConstLeaf d z) (polyTreeConstLeaf d r)) =
      (2 ^ d) * (if makeHint z r then 1 else 0)
  | 0 => by simp [polyTreeConstLeaf, makeHintTree, HintTree.weight]
  | d + 1 => by
    simp only [polyTreeConstLeaf, makeHintTree, HintTree.weight,
      polyTreeConstLeaf_hintWeight z r d, Nat.pow_succ]
    cases makeHint z r <;> simp <;> omega

/-- Non-vacuous inhabitedness witness for `highBits_az_sub_ct_eq_w1` with nonzero $A, s_1, s_2, y, c$. -/
theorem highBits_az_sub_ct_eq_w1_inhabited :
    ∃ (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256),
      c ≠ PolyTree.zero 8 ∧
      lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2)) < mldsa44Gamma2 - mldsa44Beta ∧
      infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 A s1) s2))) < mldsa44Gamma2 := by
  let p1 : Poly256 := polyTreeConstLeaf 8 Fq204.one
  let v1 : PolyVec4 := fun _ => p1
  refine ⟨idMat4, v1, v1, v1, PolyTree.constUnit 8, ?_, ?_, ?_⟩
  · decide
  · have hMv : matVecMul4 idMat4 v1 = v1 := matVecMul4_idMat4 v1
    have hMul : mulPolyVec4 (PolyTree.constUnit 8) v1 = v1 := by
      funext i; exact negacyclicMul_one_left (v1 i)
    rw [hMv, hMul]
    have hSub : subVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 Fq204.zero) := by
      funext i
      dsimp only [subVec4, v1]
      rw [polyTree_sub_eq_add_neg, polyTree_add_comm, polyTree_add_left_neg, polyTreeConstLeaf_zero_eq]
    rw [hSub]
    unfold lowBitsNormVec4
    dsimp only
    simp only [polyTreeConstLeaf_lowBitsNorm, Nat.max_self]
    decide
  · have hMv : matVecMul4 idMat4 v1 = v1 := matVecMul4_idMat4 v1
    rw [hMv]
    have hMul : ∀ w : PolyVec4, mulPolyVec4 (PolyTree.constUnit 8) w = w := fun w => by
      funext i; exact negacyclicMul_one_left (w i)
    rw [hMul]
    have hAdd : addVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 (Fq204.add Fq204.one Fq204.one)) := by
      funext i; exact polyTreeConstLeaf_add Fq204.one Fq204.one 8
    rw [hAdd]
    unfold infNormVec4 power2RoundLowVec4
    dsimp only
    simp only [polyTreeConstLeaf_power2RoundLow, polyTreeConstLeaf_infNorm, Nat.max_self]
    decide

/-! ## §2. 2-Phase Committed Threshold `ML-DSA-44` DKG & Aggregate Rejection-Barrier Security (`P0-05`–`P0-07`, `P1-09`) -/

/-! ### §2.1 Constructive Honest-Holder Coverage (`subset_honest_holder_exists`, `P0-07`) & Subset Intersection -/

def natMemBool (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => decide (x = y) || natMemBool x ys

private theorem natMemBool_eq_true_iff (x : Nat) :
    ∀ (l : List Nat), natMemBool x l = true ↔ x ∈ l
  | [] => by simp [natMemBool]
  | y :: ys => by
    simp only [natMemBool, Bool.or_eq_true, decide_eq_true_eq,
      natMemBool_eq_true_iff x ys, List.mem_cons]

private theorem natMemBool_eq_false_iff (x : Nat) (l : List Nat) :
    natMemBool x l = false ↔ x ∉ l := by
  constructor
  · intro hf hm
    rw [(natMemBool_eq_true_iff x l).mpr hm] at hf
    cases hf
  · intro hnm
    cases hb : natMemBool x l
    · rfl
    · exact False.elim (hnm ((natMemBool_eq_true_iff x l).mp hb))

private def eraseFirstNat (x : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseFirstNat x ys

private theorem eraseFirstNat_length_succ {x : Nat} :
    ∀ {l : List Nat}, natMemBool x l = true → (eraseFirstNat x l).length + 1 = l.length
  | [], h => by cases h
  | y :: ys, h => by
    dsimp only [eraseFirstNat]
    if hxy : x = y then
      simp [hxy]
    else
      simp only [natMemBool, decide_eq_false hxy, Bool.false_or] at h
      simp only [hxy, ↓reduceIte, List.length_cons]
      have ih := eraseFirstNat_length_succ h
      omega

private theorem natMemBool_eraseFirstNat_of_ne {z x : Nat} (hne : z ≠ x) :
    ∀ {l : List Nat}, natMemBool z l = true → natMemBool z (eraseFirstNat x l) = true
  | [], h => by cases h
  | y :: ys, h => by
    dsimp only [eraseFirstNat]
    if hxy : x = y then
      subst hxy
      simp only [natMemBool, decide_eq_false hne, Bool.false_or] at h
      simp [h]
    else
      simp only [hxy, ↓reduceIte, natMemBool]
      simp only [natMemBool, Bool.or_eq_true] at h
      rcases h with hzy | hTail
      · simp [hzy]
      · simp [natMemBool_eraseFirstNat_of_ne hne hTail]

private theorem natNodup_length_le_of_subset :
    ∀ {T : List Nat} (C : List Nat),
      T.Nodup →
      (∀ x ∈ T, natMemBool x C = true) →
      T.length ≤ C.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, C, hNodup, hSub => by
    rcases List.nodup_cons.mp hNodup with ⟨hxNotMem, hxsNodup⟩
    have hxMemC : natMemBool x C = true := hSub x (.head xs)
    have hLenC := eraseFirstNat_length_succ hxMemC
    have hSubTail : ∀ z ∈ xs, natMemBool z (eraseFirstNat x C) = true := by
      intro z hz
      have hzx : z ≠ x := fun hEq => hxNotMem (hEq ▸ hz)
      exact natMemBool_eraseFirstNat_of_ne hzx (hSub z (.tail x hz))
    have ih := natNodup_length_le_of_subset (eraseFirstNat x C) hxsNodup hSubTail
    simp only [List.length_cons]
    omega

/-- Constructive (`0 Classical.choice`) finder returning the first party in subset `T`
    outside corrupt set `C`. -/
def findHonestHolder (C : List Nat) : List Nat → Option Nat
  | [] => none
  | x :: xs => if natMemBool x C then findHonestHolder C xs else some x

theorem findHonestHolder_some_spec {C : List Nat} :
    ∀ {T : List Nat} {h : Nat},
      findHonestHolder C T = some h → h ∈ T ∧ h ∉ C
  | [], _, hEq => by cases hEq
  | x :: xs, h, hEq => by
    dsimp only [findHonestHolder] at hEq
    cases hb : natMemBool x C
    · rw [hb] at hEq
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hEq
      subst hEq
      exact ⟨.head xs, (natMemBool_eq_false_iff x C).mp hb⟩
    · rw [hb] at hEq
      simp only [↓reduceIte] at hEq
      obtain ⟨hInXs, hNotC⟩ := findHonestHolder_some_spec hEq
      exact ⟨.tail x hInXs, hNotC⟩

theorem findHonestHolder_none_spec {C : List Nat} :
    ∀ {T : List Nat},
      findHonestHolder C T = none → ∀ x ∈ T, natMemBool x C = true
  | [], _, _, hMem => nomatch hMem
  | x :: xs, hNone, z, hMem => by
    dsimp only [findHonestHolder] at hNone
    cases hb : natMemBool x C
    · rw [hb] at hNone; cases hNone
    · rw [hb] at hNone
      simp only [↓reduceIte] at hNone
      rcases List.mem_cons.mp hMem with rfl | hzXs
      · exact hb
      · exact findHonestHolder_none_spec hNone z hzXs

/-- Replicated subset share record $(s_{1,T}, s_{2,T}, t_T)$ verified locally by every honest holder of $T$. -/
structure SubsetShareRecord where
  s1 : PolyVec4
  s2 : PolyVec4
  publicT : PolyVec4

def polyVec4EqBool (u v : PolyVec4) : Bool :=
  decide (u ⟨0, by decide⟩ = v ⟨0, by decide⟩) &&
  decide (u ⟨1, by decide⟩ = v ⟨1, by decide⟩) &&
  decide (u ⟨2, by decide⟩ = v ⟨2, by decide⟩) &&
  decide (u ⟨3, by decide⟩ = v ⟨3, by decide⟩)

theorem polyVec4EqBool_eq_true_iff (u v : PolyVec4) :
    polyVec4EqBool u v = true ↔ u = v := by
  unfold polyVec4EqBool
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    funext i
    rcases i with ⟨idx, hidx⟩
    have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hCases with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rintro rfl
    exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩

/-- Local subset-share relation & $\ell_\infty$ bound checked by every honest holder of subset `T`. -/
def validSubsetShare (A : PolyMat4) (etaSub : Nat) (sh : SubsetShareRecord) : Bool :=
  polyVec4EqBool sh.publicT (addVec4 (matVecMul4 A sh.s1) sh.s2) &&
  decide (infNormVec4 sh.s1 ≤ etaSub) &&
  decide (infNormVec4 sh.s2 ≤ etaSub)

theorem validSubsetShare_eq_true_iff (A : PolyMat4) (etaSub : Nat) (sh : SubsetShareRecord) :
    validSubsetShare A etaSub sh = true ↔
      sh.publicT = addVec4 (matVecMul4 A sh.s1) sh.s2 ∧
      infNormVec4 sh.s1 ≤ etaSub ∧
      infNormVec4 sh.s2 ≤ etaSub := by
  unfold validSubsetShare
  simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff, decide_eq_true_eq, and_assoc]

/-- **Flagship §2.1 Theorem — Constructive Honest-Holder Coverage (`subset_honest_holder_exists`, `P0-07`)**:
    For every threshold configuration $(t, n)$ with $t \ge 1$ and $n \ge 2t - 1$, every corrupt list
    `C` (`C.Nodup`, `C.length ≤ t - 1`), and every replicated subset `T` (`T.Nodup`, `T.length = n - t + 1`):
    1. Constructive `findHonestHolder C T` (`0 Classical.choice`) returns `some h` with `h ∈ T ∧ h ∉ C`;
    2. Whenever every honest custodian `p ∉ C` enforces `validSubsetShare A etaSub sh = true` on the
       subsets `p ∈ T` it holds, subset `T` is guaranteed to satisfy both the linear relation
       `sh.publicT = A * sh.s1 + sh.s2` and the short-secret bounds `‖sh.s1‖_∞ ≤ etaSub ∧ ‖sh.s2‖_∞ ≤ etaSub`. -/
theorem subset_honest_holder_exists
    {t n : Nat} (ht : 1 ≤ t) (hn : 2 * t - 1 ≤ n)
    {C T : List Nat} (hCLen : C.length ≤ t - 1)
    (hTNodup : T.Nodup) (hTLen : T.length = n - t + 1)
    (A : PolyMat4) (etaSub : Nat) (sh : SubsetShareRecord) :
    (∃ h : Nat, findHonestHolder C T = some h ∧ h ∈ T ∧ h ∉ C) ∧
    ((∀ p : Nat, p ∈ T → p ∉ C → validSubsetShare A etaSub sh = true) →
      sh.publicT = addVec4 (matVecMul4 A sh.s1) sh.s2 ∧
      infNormVec4 sh.s1 ≤ etaSub ∧
      infNormVec4 sh.s2 ≤ etaSub) := by
  have hEx : ∃ h : Nat, findHonestHolder C T = some h ∧ h ∈ T ∧ h ∉ C := by
    cases hOpt : findHonestHolder C T with
    | some h =>
      obtain ⟨hInT, hNotC⟩ := findHonestHolder_some_spec hOpt
      exact ⟨h, rfl, hInT, hNotC⟩
    | none =>
      have hAll := findHonestHolder_none_spec hOpt
      have hLe := natNodup_length_le_of_subset C hTNodup hAll
      omega
  refine ⟨hEx, ?_⟩
  intro hHonestCheck
  rcases hEx with ⟨h, _, hInT, hNotC⟩
  exact (validSubsetShare_eq_true_iff A etaSub sh).mp (hHonestCheck h hInT hNotC)

/-- **`#tooth` (`tooth_dkg_2of2_lacks_honest_holder_coverage`)**:
    Violating $n \ge 2t - 1$ at $(t = 2, n = 2)$ ($2 < 2 \cdot 2 - 1 = 3$) shrinks replicated subsets to
    size $n - t + 1 = 1$, allowing 1 corrupt party `C = [0]` to monopolize subset `T = [0]` with
    zero honest holders (`findHonestHolder C T = none`) and forge an invalid relation $t_T \ne A s_1 + s_2$! -/
theorem tooth_dkg_2of2_lacks_honest_holder_coverage :
    let t := 2
    let n := 2
    let C : List Nat := [0]
    let T : List Nat := [0]
    let badShare : SubsetShareRecord := {
      s1 := fun _ => PolyTree.zero 8
      s2 := fun _ => PolyTree.zero 8
      publicT := fun _ => PolyTree.constUnit 8
    }
    n < 2 * t - 1 ∧
    C.Nodup ∧ C.length ≤ t - 1 ∧
    T.Nodup ∧ T.length = n - t + 1 ∧
    findHonestHolder C T = none ∧
    (∀ p : Nat, p ∈ T → p ∉ C → validSubsetShare idMat4 mldsa44Eta badShare = true) ∧
    badShare.publicT ≠ addVec4 (matVecMul4 idMat4 badShare.s1) badShare.s2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, ?_, ?_⟩
  · intro p hpT hpNotC
    rcases List.mem_singleton.mp hpT with rfl
    exact False.elim (hpNotC (.head []))
  · intro hEq
    have h0 := congrFun hEq ⟨0, by decide⟩
    have hMv := congrFun (matVecMul4_idMat4 (fun _ => PolyTree.zero 8)) ⟨0, by decide⟩
    dsimp only [addVec4] at h0
    rw [hMv, polyTree_add_zero] at h0
    revert h0; decide

/-- Constructive intersection witness for any two replicated subsets of size $n - t + 1$ when $n \ge 2t - 1$:
    `findCommonParty T₁ T₂` returns `some p` with `p ∈ T₁ ∧ p ∈ T₂` (certifying degree-2 cross-term coverage!). -/
def findCommonParty (T₁ T₂ : List Nat) : Option Nat :=
  findHonestHolder [] (T₁.filter (fun x => natMemBool x T₂))

theorem replicated_subsets_intersect
    {t n : Nat} (ht : 1 ≤ t) (hn : 2 * t - 1 ≤ n)
    {T₁ T₂ : List Nat}
    (h1Nodup : T₁.Nodup) (h2Nodup : T₂.Nodup)
    (h1Bounds : ∀ x ∈ T₁, x < n) (h2Bounds : ∀ x ∈ T₂, x < n)
    (h1Len : T₁.length = n - t + 1) (h2Len : T₂.length = n - t + 1) :
    ∃ p : Nat, p ∈ T₁ ∧ p ∈ T₂ := by
  cases hCommon : T₁.filter (fun x => natMemBool x T₂) with
  | cons p rest =>
    have hpMem : p ∈ T₁.filter (fun x => natMemBool x T₂) := by rw [hCommon]; exact .head rest
    rw [List.mem_filter] at hpMem
    exact ⟨p, hpMem.1, (natMemBool_eq_true_iff p T₂).mp hpMem.2⟩
  | nil =>
    have hDisj : ∀ a ∈ T₁, ∀ b ∈ T₂, a ≠ b := by
      intro a ha b hb hEq
      subst hEq
      have haFilt : a ∈ T₁.filter (fun x => natMemBool x T₂) :=
        List.mem_filter.mpr ⟨ha, (natMemBool_eq_true_iff a T₂).mpr hb⟩
      rw [hCommon] at haFilt
      cases haFilt
    have hAppNodup : (T₁ ++ T₂).Nodup := List.nodup_append.mpr ⟨h1Nodup, h2Nodup, hDisj⟩
    have hInRange : ∀ z ∈ T₁ ++ T₂, natMemBool z (List.range n) = true := by
      intro z hz
      rw [natMemBool_eq_true_iff, List.mem_range]
      rcases List.mem_append.mp hz with hz1 | hz2
      · exact h1Bounds z hz1
      · exact h2Bounds z hz2
    have hLe := natNodup_length_le_of_subset (List.range n) hAppNodup hInRange
    rw [List.length_append, List.length_range] at hLe
    omega

/-! ### §2.2 Exact 4-Bit Algebraic Nibble Rejection Circuit (`dkg_nibble_rejection_circuit_exact`, `P1-09`) -/

/-- Exact 4-bit MPC nibble circuit from `threshold_mldsa.rs:377-392` over `Fq204`,
    returning `(is15, coeff)` where `coeff = 2 - (nib mod 5)` for all `nib < 15`. -/
def dkgNibbleCircuit (b0 b1 b2 b3 : Fq204) : Fq204 × Fq204 :=
  let p01 := Fq204.mul b0 b1
  let p12 := Fq204.mul b1 b2
  let p23 := Fq204.mul b2 b3
  let or12 := Fq204.sub (Fq204.add b1 b2) p12
  let or01 := Fq204.sub (Fq204.add b0 b1) p01
  let atLeast10 := Fq204.mul b3 or12
  let lowPart := Fq204.mul b2 or01
  let is15 := Fq204.mul p01 p23
  let atLeast5 := Fq204.sub (Fq204.add b3 lowPart) (Fq204.mul b3 lowPart)
  let comp :=
    Fq204.add (Fq204.add b0 (Fq204.mul (Fq204.ofNat 2) b1))
              (Fq204.add (Fq204.mul (Fq204.ofNat 4) b2) (Fq204.mul (Fq204.ofNat 8) b3))
  let coeff :=
    Fq204.add (Fq204.sub (Fq204.ofNat 2) comp)
              (Fq204.mul (Fq204.ofNat 5) (Fq204.add atLeast5 atLeast10))
  (is15, coeff)

def nibbleBitsToFq204 (nib : Nat) : Fq204 × Fq204 × Fq204 × Fq204 :=
  (Fq204.ofNat (nib % 2),
   Fq204.ofNat ((nib / 2) % 2),
   Fq204.ofNat ((nib / 4) % 2),
   Fq204.ofNat ((nib / 8) % 2))

def evalNibbleCircuitNat (nib : Nat) : Fq204 × Fq204 :=
  let (b0, b1, b2, b3) := nibbleBitsToFq204 nib
  dkgNibbleCircuit b0 b1 b2 b3

/-- **Exact 4-Bit DKG Nibble Rejection & Uniformity Theorem (`dkg_nibble_rejection_circuit_exact`, `P1-09`)**:
    1. Over all 16 4-bit inputs `nib ∈ [0, 16)`, `is15 = 1 ↔ nib = 15` and `is15 = 0 ↔ nib < 15`;
    2. For all 15 accepted nibbles `nib < 15`, `coeff = Fq204.ofInt (2 - (nib % 5))` with
       `centeredAbs coeff ≤ mldsa44Eta` (`= 2`);
    3. Every target coefficient in `{-2, -1, 0, 1, 2}` has **exact multiplicity 3** across `[0, 15)`
       (zero modulo bias), whereas `#tooth` omitting `nib = 15` rejection admits `(evalNibbleCircuitNat 15).2 = -3`
       with `centeredAbs = 3 > mldsa44Eta`, violating the short-key norm bound! -/
theorem dkg_nibble_rejection_circuit_exact :
    (∀ nib : Fin 16,
      ((evalNibbleCircuitNat nib.val).1 = Fq204.one ↔ nib.val = 15) ∧
      ((evalNibbleCircuitNat nib.val).1 = Fq204.zero ↔ nib.val < 15) ∧
      (nib.val < 15 →
        (evalNibbleCircuitNat nib.val).2 = Fq204.ofInt (2 - ((nib.val % 5 : Nat) : Int)) ∧
        Fq204.centeredAbs (evalNibbleCircuitNat nib.val).2 ≤ mldsa44Eta)) ∧
    (∀ k ∈ ([-2, -1, 0, 1, 2] : List Int),
      ((List.range 15).filter (fun nib => decide ((evalNibbleCircuitNat nib).2 = Fq204.ofInt k))).length = 3) ∧
    ((evalNibbleCircuitNat 15).2 = Fq204.ofInt (-3) ∧
     mldsa44Eta < Fq204.centeredAbs (evalNibbleCircuitNat 15).2) := by
  decide

/-! ### §2.3 2-Phase Salted Commitment Anti-Rogue-Key Theorem (`dkg_phase2_commit_blocks_rogue_key`, `P0-05`) -/

/-- Canonical fixed-width byte encoding of a $2^d$-coefficient `PolyTree` (`4 * 2^d` bytes). -/
def encodePolyTreeBytes : {d : Nat} → PolyTree d → List UInt8
  | 0, .leaf x => encodeU32BeNat x.val
  | _ + 1, .branch l r => encodePolyTreeBytes l ++ encodePolyTreeBytes r

theorem encodePolyTreeBytes_length : ∀ {d : Nat} (p : PolyTree d),
    (encodePolyTreeBytes p).length = 4 * (2 ^ d)
  | 0, .leaf x => by simp [encodePolyTreeBytes, encodeU32BeNat_length]
  | d + 1, .branch l r => by
    simp only [encodePolyTreeBytes, List.length_append,
      encodePolyTreeBytes_length l, encodePolyTreeBytes_length r, Nat.pow_succ]
    omega

private theorem append_inj_of_eq_len {α : Type} :
    ∀ {l1 r1 l2 r2 : List α},
      l1.length = l2.length →
      l1 ++ r1 = l2 ++ r2 →
      l1 = l2 ∧ r1 = r2
  | [], r1, [], r2, _, hEq => ⟨rfl, hEq⟩
  | _ :: _, _, [], _, hLen, _ => by cases hLen
  | [], _, _ :: _, _, hLen, _ => by cases hLen
  | a :: l1, r1, b :: l2, r2, hLen, hEq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    injection hEq with hHead hTail
    obtain ⟨hL, hR⟩ := append_inj_of_eq_len hLen hTail
    exact ⟨by rw [hHead, hL], hR⟩

theorem encodePolyTreeBytes_injective : ∀ {d : Nat} {p q : PolyTree d},
    encodePolyTreeBytes p = encodePolyTreeBytes q → p = q
  | 0, .leaf x, .leaf y, hEq => by
    dsimp only [encodePolyTreeBytes] at hEq
    have hxLt : x.val < 2 ^ 32 := Nat.lt_trans x.isLt (by decide)
    have hyLt : y.val < 2 ^ 32 := Nat.lt_trans y.isLt (by decide)
    have hDec := congrArg decodeU32BeNat hEq
    rw [decodeU32BeNat_encodeU32BeNat hxLt, decodeU32BeNat_encodeU32BeNat hyLt] at hDec
    injection hDec with hVal
    exact congrArg PolyTree.leaf (Fq204.ext hVal)
  | d + 1, .branch l1 r1, .branch l2 r2, hEq => by
    have hLen : (encodePolyTreeBytes l1).length = (encodePolyTreeBytes l2).length := by
      rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
    obtain ⟨hL, hR⟩ := append_inj_of_eq_len hLen hEq
    rw [encodePolyTreeBytes_injective hL, encodePolyTreeBytes_injective hR]

/-- Fixed 4096-byte canonical serialization of `PolyVec4` (`4 * 1024 = 4096` bytes). -/
def encodePolyVec4Bytes (v : PolyVec4) : List UInt8 :=
  encodePolyTreeBytes (v ⟨0, by decide⟩) ++
  encodePolyTreeBytes (v ⟨1, by decide⟩) ++
  encodePolyTreeBytes (v ⟨2, by decide⟩) ++
  encodePolyTreeBytes (v ⟨3, by decide⟩)

theorem encodePolyVec4Bytes_length (v : PolyVec4) :
    (encodePolyVec4Bytes v).length = 4096 := by
  unfold encodePolyVec4Bytes
  simp only [List.length_append, encodePolyTreeBytes_length]

theorem encodePolyVec4Bytes_injective {u v : PolyVec4}
    (hEq : encodePolyVec4Bytes u = encodePolyVec4Bytes v) : u = v := by
  unfold encodePolyVec4Bytes at hEq
  simp only [List.append_assoc] at hEq
  have hL0 : (encodePolyTreeBytes (u ⟨0, by decide⟩)).length =
      (encodePolyTreeBytes (v ⟨0, by decide⟩)).length := by
    rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
  obtain ⟨e0, r0⟩ := append_inj_of_eq_len hL0 hEq
  have hL1 : (encodePolyTreeBytes (u ⟨1, by decide⟩)).length =
      (encodePolyTreeBytes (v ⟨1, by decide⟩)).length := by
    rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
  obtain ⟨e1, r1⟩ := append_inj_of_eq_len hL1 r0
  have hL2 : (encodePolyTreeBytes (u ⟨2, by decide⟩)).length =
      (encodePolyTreeBytes (v ⟨2, by decide⟩)).length := by
    rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
  obtain ⟨e2, e3⟩ := append_inj_of_eq_len hL2 r1
  have p0 := encodePolyTreeBytes_injective e0
  have p1 := encodePolyTreeBytes_injective e1
  have p2 := encodePolyTreeBytes_injective e2
  have p3 := encodePolyTreeBytes_injective e3
  funext i
  rcases i with ⟨idx, hidx⟩
  have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl
  · exact p0
  · exact p1
  · exact p2
  · exact p3

private theorem ite_true_of {α : Type} {c : Prop} [Decidable c] (h : c) (t e : α) :
    (if c then t else e) = t := by
  split <;> rename_i hc
  · rfl
  · exact False.elim (hc h)

private theorem ite_false_of {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (t e : α) :
    (if c then t else e) = e := by
  split <;> rename_i hc
  · exact False.elim (h hc)
  · rfl

/-- Exact little-endian `u64` frame body `(u64_le(f.len()) || f)*` matching
    `qsag_accel::keccak::cshake256_framed_xof` (`keccak.rs:281-284`). -/
def encodeFramesU64LeBody : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => (encodeNatLeBytes 8 f.length ++ f) ++ encodeFramesU64LeBody fs

/-- Exact little-endian `u64` framed slice list `u64_le(frames.len()) || (u64_le(f.len()) || f)*`
    matching `qsag_accel::keccak::cshake256_framed_xof` (`keccak.rs:280-284`). -/
def encodeFramesU64Le (frames : List (List UInt8)) : List UInt8 :=
  encodeNatLeBytes 8 frames.length ++ encodeFramesU64LeBody frames

private theorem encodeFramesU64LeBody_injective_of_len :
    ∀ {fs gs : List (List UInt8)},
      fs.length = gs.length →
      (∀ f ∈ fs, f.length < 256 ^ 8) →
      (∀ g ∈ gs, g.length < 256 ^ 8) →
      encodeFramesU64LeBody fs = encodeFramesU64LeBody gs →
      fs = gs
  | [], [], _, _, _, _ => rfl
  | f :: fs, g :: gs, hCnt, hfB, hgB, hEq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hCnt
    dsimp only [encodeFramesU64LeBody] at hEq
    rw [List.append_assoc, List.append_assoc] at hEq
    have hL8 : (encodeNatLeBytes 8 f.length).length = (encodeNatLeBytes 8 g.length).length := by
      rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
    obtain ⟨hLenBytes, hRest⟩ := append_inj_of_eq_len hL8 hEq
    have hfLt : f.length < 256 ^ 8 := hfB f (.head fs)
    have hgLt : g.length < 256 ^ 8 := hgB g (.head gs)
    have hDec := congrArg decodeNatLeBytes hLenBytes
    rw [decodeNatLeBytes_encodeNatLeBytes 8 f.length hfLt,
        decodeNatLeBytes_encodeNatLeBytes 8 g.length hgLt] at hDec
    obtain ⟨hFG, hTail⟩ := append_inj_of_eq_len hDec hRest
    have hTailEq := encodeFramesU64LeBody_injective_of_len hCnt
      (fun x hx => hfB x (.tail f hx)) (fun y hy => hgB y (.tail g hy)) hTail
    rw [hFG, hTailEq]

theorem encodeFramesU64Le_injective {fs gs : List (List UInt8)}
    (hCntF : fs.length < 256 ^ 8) (hCntG : gs.length < 256 ^ 8)
    (hfB : ∀ f ∈ fs, f.length < 256 ^ 8)
    (hgB : ∀ g ∈ gs, g.length < 256 ^ 8)
    (hEq : encodeFramesU64Le fs = encodeFramesU64Le gs) : fs = gs := by
  unfold encodeFramesU64Le at hEq
  have hL8 : (encodeNatLeBytes 8 fs.length).length = (encodeNatLeBytes 8 gs.length).length := by
    rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
  obtain ⟨hCntBytes, hBodyEq⟩ := append_inj_of_eq_len hL8 hEq
  have hCntEq : fs.length = gs.length := by
    have hd := congrArg decodeNatLeBytes hCntBytes
    rwa [decodeNatLeBytes_encodeNatLeBytes 8 fs.length hCntF,
         decodeNatLeBytes_encodeNatLeBytes 8 gs.length hCntG] at hd
  exact encodeFramesU64LeBody_injective_of_len hCntEq hfB hgB hBodyEq

/-- Exact SP 800-185 + `u64_le` sponge preimage absorbed by `cshake256_framed_xof` (`keccak.rs:277-286`). -/
def cshake256FramedPreimage (customization : List UInt8) (frames : List (List UInt8)) : List UInt8 :=
  if customization = [] then
    encodeFramesU64Le frames
  else
    customizationPrefix customization ++ encodeFramesU64Le frames

/-- Concrete 32-byte `cshake256_framed_32` matching `qsag_accel::keccak::cshake256_framed_32` (`keccak.rs:291-295`). -/
def cshake256FramedBytes (customization : List UInt8) (frames : List (List UInt8)) : List UInt8 :=
  cshake256Bytes customization (encodeFramesU64Le frames)

theorem cshake256FramedBytes_eq_sponge (customization : List UInt8) (frames : List (List UInt8)) :
    cshake256FramedBytes customization frames =
      squeezeXofAux 32 (absorbPadded (padForRate
        (cshake256FramedPreimage customization frames)
        (if customization = [] then 0x1f else 0x04))) := by
  unfold cshake256FramedBytes cshake256FramedPreimage cshake256Bytes cshake256Xof
  rfl

@[simp] theorem cshake256FramedBytes_length (customization : List UInt8) (frames : List (List UInt8)) :
    (cshake256FramedBytes customization frames).length = 32 := by
  unfold cshake256FramedBytes
  exact cshake256Bytes_length customization (encodeFramesU64Le frames)

theorem cshake256FramedPreimage_frames_injective {customization : List UInt8}
    {fs gs : List (List UInt8)}
    (hCntF : fs.length < 256 ^ 8) (hCntG : gs.length < 256 ^ 8)
    (hfB : ∀ f ∈ fs, f.length < 256 ^ 8)
    (hgB : ∀ g ∈ gs, g.length < 256 ^ 8)
    (hEq : cshake256FramedPreimage customization fs = cshake256FramedPreimage customization gs) :
    fs = gs := by
  unfold cshake256FramedPreimage at hEq
  if hEmpty : customization = [] then
    rw [ite_true_of hEmpty, ite_true_of hEmpty] at hEq
    exact encodeFramesU64Le_injective hCntF hCntG hfB hgB hEq
  else
    rw [ite_false_of hEmpty, ite_false_of hEmpty] at hEq
    obtain ⟨_, hFrEq⟩ := append_inj_of_eq_len rfl hEq
    exact encodeFramesU64Le_injective hCntF hCntG hfB hgB hFrEq

/-- Little-endian `u32` (`v.to_le_bytes()`) polynomial serialization matching `threshold_mldsa.rs:615-618`. -/
def encodePolyTreeBytesLe : {d : Nat} → PolyTree d → List UInt8
  | 0, .leaf x => encodeNatLeBytes 4 x.val
  | _ + 1, .branch l r => encodePolyTreeBytesLe l ++ encodePolyTreeBytesLe r

theorem encodePolyTreeBytesLe_length : ∀ {d : Nat} (p : PolyTree d),
    (encodePolyTreeBytesLe p).length = 4 * (2 ^ d)
  | 0, .leaf x => by simp [encodePolyTreeBytesLe, encodeNatLeBytes_length]
  | d + 1, .branch l r => by
    simp only [encodePolyTreeBytesLe, List.length_append,
      encodePolyTreeBytesLe_length l, encodePolyTreeBytesLe_length r, Nat.pow_succ]
    omega

theorem encodePolyTreeBytesLe_injective : ∀ {d : Nat} {p q : PolyTree d},
    encodePolyTreeBytesLe p = encodePolyTreeBytesLe q → p = q
  | 0, .leaf x, .leaf y, hEq => by
    dsimp only [encodePolyTreeBytesLe] at hEq
    have hxLt : x.val < 256 ^ 4 := Nat.lt_trans x.isLt (by decide)
    have hyLt : y.val < 256 ^ 4 := Nat.lt_trans y.isLt (by decide)
    have hDec := congrArg decodeNatLeBytes hEq
    rw [decodeNatLeBytes_encodeNatLeBytes 4 x.val hxLt,
        decodeNatLeBytes_encodeNatLeBytes 4 y.val hyLt] at hDec
    exact congrArg PolyTree.leaf (Fq204.ext hDec)
  | _ + 1, .branch l1 r1, .branch l2 r2, hEq => by
    have hLen : (encodePolyTreeBytesLe l1).length = (encodePolyTreeBytesLe l2).length := by
      rw [encodePolyTreeBytesLe_length, encodePolyTreeBytesLe_length]
    obtain ⟨hL, hR⟩ := append_inj_of_eq_len hLen hEq
    rw [encodePolyTreeBytesLe_injective hL, encodePolyTreeBytesLe_injective hR]

/-- Fixed 4096-byte little-endian canonical serialization of `PolyVec4` (`threshold_mldsa.rs:615-618`). -/
def encodePolyVec4BytesLe (v : PolyVec4) : List UInt8 :=
  encodePolyTreeBytesLe (v ⟨0, by decide⟩) ++
  encodePolyTreeBytesLe (v ⟨1, by decide⟩) ++
  encodePolyTreeBytesLe (v ⟨2, by decide⟩) ++
  encodePolyTreeBytesLe (v ⟨3, by decide⟩)

theorem encodePolyVec4BytesLe_length (v : PolyVec4) :
    (encodePolyVec4BytesLe v).length = 4096 := by
  unfold encodePolyVec4BytesLe
  simp only [List.length_append, encodePolyTreeBytesLe_length]

theorem encodePolyVec4BytesLe_injective {u v : PolyVec4}
    (hEq : encodePolyVec4BytesLe u = encodePolyVec4BytesLe v) : u = v := by
  unfold encodePolyVec4BytesLe at hEq
  simp only [List.append_assoc] at hEq
  have hL0 : (encodePolyTreeBytesLe (u ⟨0, by decide⟩)).length =
      (encodePolyTreeBytesLe (v ⟨0, by decide⟩)).length := by
    rw [encodePolyTreeBytesLe_length, encodePolyTreeBytesLe_length]
  obtain ⟨e0, r0⟩ := append_inj_of_eq_len hL0 hEq
  have hL1 : (encodePolyTreeBytesLe (u ⟨1, by decide⟩)).length =
      (encodePolyTreeBytesLe (v ⟨1, by decide⟩)).length := by
    rw [encodePolyTreeBytesLe_length, encodePolyTreeBytesLe_length]
  obtain ⟨e1, r1⟩ := append_inj_of_eq_len hL1 r0
  have hL2 : (encodePolyTreeBytesLe (u ⟨2, by decide⟩)).length =
      (encodePolyTreeBytesLe (v ⟨2, by decide⟩)).length := by
    rw [encodePolyTreeBytesLe_length, encodePolyTreeBytesLe_length]
  obtain ⟨e2, e3⟩ := append_inj_of_eq_len hL2 r1
  have p0 := encodePolyTreeBytesLe_injective e0
  have p1 := encodePolyTreeBytesLe_injective e1
  have p2 := encodePolyTreeBytesLe_injective e2
  have p3 := encodePolyTreeBytesLe_injective e3
  funext ⟨idx, hidx⟩
  have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl
  · exact p0
  · exact p1
  · exact p2
  · exact p3

/-- Degree-6 verification extension field $\mathbb{F}_q[X]/(X^6 - 7)$ (`EXT_DEGREE = 6`, `EXT_NONRESIDUE = 7`,
    `rss_mpc.rs:52-56`) used by `rss_mpc::Engine` batch inner-product multiplication verification. -/
structure Ext6Fq204 where
  a0 : Fq204
  a1 : Fq204
  a2 : Fq204
  a3 : Fq204
  a4 : Fq204
  a5 : Fq204
  deriving DecidableEq, Repr

def ext6Zero : Ext6Fq204 := ⟨Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩
def ext6Nonresidue : Fq204 := Fq204.ofNat 7

def ext6EmbedFq (x : Fq204) : Ext6Fq204 :=
  ⟨x, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩

def ext6Add (x y : Ext6Fq204) : Ext6Fq204 :=
  ⟨Fq204.add x.a0 y.a0, Fq204.add x.a1 y.a1, Fq204.add x.a2 y.a2,
   Fq204.add x.a3 y.a3, Fq204.add x.a4 y.a4, Fq204.add x.a5 y.a5⟩

def ext6Sub (x y : Ext6Fq204) : Ext6Fq204 :=
  ⟨Fq204.sub x.a0 y.a0, Fq204.sub x.a1 y.a1, Fq204.sub x.a2 y.a2,
   Fq204.sub x.a3 y.a3, Fq204.sub x.a4 y.a4, Fq204.sub x.a5 y.a5⟩

/-- Base-field scalar multiplication `k_scale(x, s)` in $\mathbb{F}_q[X]/(X^6 - 7)$ (`rss_mpc.rs:336-338`). -/
def ext6Scale (x : Ext6Fq204) (s : Fq204) : Ext6Fq204 :=
  ⟨Fq204.mul x.a0 s, Fq204.mul x.a1 s, Fq204.mul x.a2 s,
   Fq204.mul x.a3 s, Fq204.mul x.a4 s, Fq204.mul x.a5 s⟩

/-- Multiplication in $\mathbb{F}_q[X]/(X^6 - 7)$ (`rss_mpc.rs:53-56`, reducing $X^{6+k} \mapsto 7 X^k$). -/
def ext6Mul (x y : Ext6Fq204) : Ext6Fq204 :=
  let nr := ext6Nonresidue
  let m (a b : Fq204) := Fq204.mul a b
  let ad (a b : Fq204) := Fq204.add a b
  let hi0 := ad (m x.a1 y.a5) (ad (m x.a2 y.a4) (ad (m x.a3 y.a3) (ad (m x.a4 y.a2) (m x.a5 y.a1))))
  let hi1 := ad (m x.a2 y.a5) (ad (m x.a3 y.a4) (ad (m x.a4 y.a3) (m x.a5 y.a2)))
  let hi2 := ad (m x.a3 y.a5) (ad (m x.a4 y.a4) (m x.a5 y.a3))
  let hi3 := ad (m x.a4 y.a5) (m x.a5 y.a4)
  let hi4 := m x.a5 y.a5
  ⟨ad (m x.a0 y.a0) (m nr hi0),
   ad (ad (m x.a0 y.a1) (m x.a1 y.a0)) (m nr hi1),
   ad (ad (m x.a0 y.a2) (ad (m x.a1 y.a1) (m x.a2 y.a0))) (m nr hi2),
   ad (ad (m x.a0 y.a3) (ad (m x.a1 y.a2) (ad (m x.a2 y.a1) (m x.a3 y.a0)))) (m nr hi3),
   ad (ad (m x.a0 y.a4) (ad (m x.a1 y.a3) (ad (m x.a2 y.a2) (ad (m x.a3 y.a1) (m x.a4 y.a0))))) (m nr hi4),
   ad (m x.a0 y.a5) (ad (m x.a1 y.a4) (ad (m x.a2 y.a3) (ad (m x.a3 y.a2) (ad (m x.a4 y.a1) (m x.a5 y.a0)))))⟩

private theorem fq204_add_sub_cancel_left (r v : Fq204) : Fq204.sub (Fq204.add r v) r = v := by
  rw [← Fq204.ofInt_nat r, ← Fq204.ofInt_nat v, Fq204.ofInt_add, Fq204.ofInt_sub]
  congr 1; omega

private theorem fq204_sub_add_cancel_left (r y : Fq204) : Fq204.add r (Fq204.sub y r) = y := by
  rw [← Fq204.ofInt_nat r, ← Fq204.ofInt_nat y, Fq204.ofInt_sub, Fq204.ofInt_add]
  congr 1; omega

private theorem ext6Add_sub_cancel (rest v : Ext6Fq204) : ext6Sub (ext6Add rest v) rest = v := by
  rcases rest with ⟨r0, r1, r2, r3, r4, r5⟩
  rcases v with ⟨v0, v1, v2, v3, v4, v5⟩
  simp only [ext6Add, ext6Sub, fq204_add_sub_cancel_left]

private theorem ext6Sub_add_cancel (rest y : Ext6Fq204) : ext6Add rest (ext6Sub y rest) = y := by
  rcases rest with ⟨r0, r1, r2, r3, r4, r5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  simp only [ext6Add, ext6Sub, fq204_sub_add_cancel_left]

private theorem ext6Scale_mul (x : Ext6Fq204) (a b : Fq204) :
    ext6Scale (ext6Scale x a) b = ext6Scale x (Fq204.mul a b) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Scale, Fq204.mul_assoc]

private theorem ext6Scale_one (x : Ext6Fq204) : ext6Scale x Fq204.one = x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Scale, Fq204.mul_one]

/-- Constructive `Ext6Fq204` bijection `chi ↦ rest + k_scale(chi, delta)` for any nonzero gate error
    `delta ≠ 0` (`rss_mpc.rs:1066-1095`): proves that across all $q^6 = 8380417^6 > 2^{137}$ extension
    challenges `chi : Ext6Fq204`, **at most one** `chi` cancels `rest` to `ext6Zero`! -/
def ext6BatchChallengeEquiv (delta : Fq204) (hDelta : delta ≠ Fq204.zero) (rest : Ext6Fq204) :
    SimpleEquiv Ext6Fq204 Ext6Fq204 where
  toFun chi := ext6Add rest (ext6Scale chi delta)
  invFun out := ext6Scale (ext6Sub out rest) (Fq204.inv delta)
  left_inv chi := by
    rw [ext6Add_sub_cancel, ext6Scale_mul, Fq204.mul_inv_cancel hDelta, ext6Scale_one]
  right_inv out := by
    rw [ext6Scale_mul, Fq204.mul_comm (Fq204.inv delta) delta, Fq204.mul_inv_cancel hDelta,
        ext6Scale_one, ext6Sub_add_cancel]

private def fq204PowModAux (base : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, exp, acc =>
    if exp = 0 then acc
    else
      let acc' := if exp % 2 = 1 then (acc * base) % mldsaQ else acc
      fq204PowModAux ((base * base) % mldsaQ) fuel (exp / 2) acc'

def fq204PowModNat (base exp : Nat) : Nat :=
  fq204PowModAux (base % mldsaQ) 28 exp 1

private theorem nodup_map_on_list_fq {α β : Type} (f : α → β) :
    ∀ {xs : List α}, xs.Nodup → (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) → (xs.map f).Nodup
  | [], _, _ => .nil
  | x :: xs, .cons hNotMem hTail, hInj => by
    simp only [List.map_cons]
    refine .cons ?_ (nodup_map_on_list_fq f hTail (fun a ha b hb => hInj a (.tail _ ha) b (.tail _ hb)))
    intro y hy hEq
    rcases List.mem_map.mp hy with ⟨z, hzMem, rfl⟩
    have hxz := hInj x (.head _) z (.tail _ hzMem) hEq
    exact hNotMem z hzMem hxz

private theorem exists_mem_of_filter_length_lt_fq {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.filter p).length < xs.length → ∃ x ∈ xs, p x = false
  | [], h => by simp at h
  | x :: xs, h => by
    cases hpx : p x
    · exact ⟨x, .head _, hpx⟩
    · simp only [List.filter_cons_of_pos hpx, List.length_cons] at h
      obtain ⟨y, hyMem, hyFalse⟩ := exists_mem_of_filter_length_lt_fq p xs (by omega)
      exact ⟨y, .tail _ hyMem, hyFalse⟩

private theorem exists_eval_nonzero_fq204 :
    ∀ (cs : List Fq204), cs.length < mldsaQ →
      (∃ c ∈ cs, c ≠ Fq204.zero) →
      ∃ x : Fq204, RoundPoly.evalCoeffs cs x ≠ CommRingOps.zero
  | [], _, ⟨_, hMem, _⟩ => by cases hMem
  | c₀ :: tail, hLen, ⟨c, hMem, hcNe⟩ => by
    if hc0Ne : c₀ ≠ Fq204.zero then
      refine ⟨Fq204.zero, ?_⟩
      change Fq204.add c₀ (Fq204.mul Fq204.zero (RoundPoly.evalCoeffs tail Fq204.zero)) ≠ Fq204.zero
      rw [Fq204.zero_mul, Fq204.add_zero]
      exact hc0Ne
    else
      have hc0Eq : c₀ = Fq204.zero := by
        cases decEq c₀ Fq204.zero with
        | isTrue h => exact h
        | isFalse h => exact False.elim (hc0Ne h)
      subst hc0Eq
      have hTailEx : ∃ c' ∈ tail, c' ≠ Fq204.zero := by
        rcases List.mem_cons.mp hMem with rfl | hInTail
        · exact False.elim (hcNe rfl)
        · exact ⟨c, hInTail, hcNe⟩
      have hTailPos : 1 ≤ tail.length := by
        rcases hTailEx with ⟨_, hm, _⟩
        cases tail with
        | nil => cases hm
        | cons _ _ => simp only [List.length_cons]; omega
      simp only [List.length_cons] at hLen
      obtain ⟨x₁, hx₁⟩ := exists_eval_nonzero_fq204 tail (by omega) hTailEx
      let d := tail.length - 1
      let grid : List Fq204 := (List.range (d + 1)).map (fun i => Fq204.ofNat (i + 1))
      have hGridLen : grid.length = d + 1 := by simp [grid]
      have hGridNodup : grid.Nodup := by
        apply nodup_map_on_list_fq _ (Qsag.Constructive.nodup_range (d + 1))
        intro a ha b hb hEq
        have haLt : a + 1 < mldsaQ := by have := List.mem_range.mp ha; omega
        have hbLt : b + 1 < mldsaQ := by have := List.mem_range.mp hb; omega
        have hVal := congrArg Fq204.val hEq
        simp only [Fq204.ofNat_val, Nat.mod_eq_of_lt haLt, Nat.mod_eq_of_lt hbLt] at hVal
        omega
      have hRootsLe :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = CommRingOps.zero))).length ≤ d :=
        RoundPoly.roots_nodup_length_le d tail grid hGridNodup (by omega) ⟨x₁, hx₁⟩
      have hFiltLt :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = CommRingOps.zero))).length < grid.length := by
        rw [hGridLen]; omega
      obtain ⟨x₀, hx₀Mem, hx₀False⟩ := exists_mem_of_filter_length_lt_fq
        (fun r => decide (RoundPoly.evalCoeffs tail r = CommRingOps.zero)) grid hFiltLt
      have hx₀NeZero : x₀ ≠ Fq204.zero := by
        rcases List.mem_map.mp hx₀Mem with ⟨idx, hIdxRange, rfl⟩
        have hIdxLt : idx + 1 < mldsaQ := by have := List.mem_range.mp hIdxRange; omega
        intro hZero
        have hv := congrArg Fq204.val hZero
        simp only [Fq204.ofNat_val, Nat.mod_eq_of_lt hIdxLt, Fq204.zero_val] at hv
        omega
      have hEvalTailNe : RoundPoly.evalCoeffs tail x₀ ≠ CommRingOps.zero := by
        intro hZero
        rw [decide_eq_true hZero] at hx₀False
        cases hx₀False
      refine ⟨x₀, ?_⟩
      change Fq204.add Fq204.zero (Fq204.mul x₀ (RoundPoly.evalCoeffs tail x₀)) ≠ Fq204.zero
      rw [Fq204.zero_add]
      intro hProdZero
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hProdZero with h1 | h2
      · exact hx₀NeZero h1
      · exact hEvalTailNe h2

/-- **Numeric Modulus Certificate & Base-Scalar Batch Bound for $\mathbb{F}_q[X]/(X^6 - 7)$ (`rss_mpc.rs:53-56, 1066-1206`)**:
    1. Serret–Kummer binomial irreducibility certificate for $X^6 - 7$ over $\mathbb{F}_{8380417}$:
       $6 \mid (q - 1)$, $7^{(q-1)/2} \equiv q - 1 \not\equiv 1 \pmod q$ ($7$ is a quadratic non-residue),
       $7^{(q-1)/3} \not\equiv 1 \pmod q$ ($7$ is a cubic non-residue), and $2^{137} < q^6$.
    2. Unique `Ext6Fq204` batch root: for any nonzero base-field gate error $\Delta \ne 0$ and arbitrary
       batch accumulator `rest`, `ext6Add rest (ext6Scale chi Δ) = ext6Zero` holds for **at most 1**
       challenge `chi : Ext6Fq204` (`(ext6BatchChallengeEquiv Δ hΔ rest).invFun ext6Zero`).
    3. Recursive polynomial folding bound (`rss_mpc.rs:1120-1171`, `FOLD = 8`): any degree-$\le D$
       ($D + 1 < q$) folding discrepancy polynomial with a nonzero coefficient has $\le D$ roots
       in any duplicate-free point set `S : List Fq204`. -/
theorem rss_ext6_modulus_certificate_and_batch_sacrifice_sound :
    ((mldsaQ - 1) % 6 = 0 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 2) = mldsaQ - 1 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 2) ≠ 1 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 3) ≠ 1 ∧
     2 ^ 137 < mldsaQ ^ 6) ∧
    (∀ (delta : Fq204) (_hDelta : delta ≠ Fq204.zero) (rest chi₁ chi₂ : Ext6Fq204),
      ext6Add rest (ext6Scale chi₁ delta) = ext6Zero →
      ext6Add rest (ext6Scale chi₂ delta) = ext6Zero →
      chi₁ = chi₂) ∧
    (∀ (D : Nat) (cs S : List Fq204),
      D + 1 < mldsaQ →
      cs.length ≤ D + 1 →
      S.Nodup →
      (∃ c ∈ cs, c ≠ Fq204.zero) →
      (S.filter (fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero))).length ≤ D) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro delta hDelta rest chi₁ chi₂ h1 h2
    let eqv := ext6BatchChallengeEquiv delta hDelta rest
    have hEq : eqv.toFun chi₁ = eqv.toFun chi₂ := h1.trans h2.symm
    have hInv := congrArg eqv.invFun hEq
    rwa [eqv.left_inv, eqv.left_inv] at hInv
  · intro D cs S hDLt hLen hNodup hNz
    obtain ⟨x₀, hx₀⟩ := exists_eval_nonzero_fq204 cs (by omega) hNz
    exact RoundPoly.roots_nodup_length_le D cs S hNodup hLen ⟨x₀, hx₀⟩

/-- Domain tag `"QSAG.RSS.VIEW.DIGEST.V1"` (`rss_mpc.rs:1180`, 23 bytes). -/
def rssViewDigestTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x52, 0x53, 0x53, 0x2E, 0x56, 0x49, 0x45,
   0x57, 0x2E, 0x44, 0x49, 0x47, 0x45, 0x53, 0x54, 0x2E, 0x56, 0x31]

def rssViewDigestPreimage (seedKey viewBytes : List UInt8) : List UInt8 :=
  cshake256FramedPreimage rssViewDigestTag [seedKey, viewBytes]

/-- Domain tag `"QSAG.TMLDSA.DKG.CONFIRM.V1"` (`threshold_mldsa.rs:582`, 26 bytes). -/
def dkgConfirmDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4D, 0x4C, 0x44, 0x53, 0x41, 0x2E, 0x44, 0x4B,
   0x47, 0x2E, 0x43, 0x4F, 0x4E, 0x46, 0x49, 0x52, 0x4D, 0x2E, 0x56, 0x31]

/-- Exact `cshake256_framed_32(b"QSAG.TMLDSA.DKG.CONFIRM.V1", &[session_id, &matrix_seed, &pk_bytes])`
    preimage (`threshold_mldsa.rs:581-585`). -/
def dkgConfirmPreimage (sessionId matrixSeed pkBytes : List UInt8) : List UInt8 :=
  cshake256FramedPreimage dkgConfirmDomainTag [sessionId, matrixSeed, pkBytes]

def dkgConfirmDigest (H : List UInt8 → List UInt8) (sessionId matrixSeed pkBytes : List UInt8) : List UInt8 :=
  H (dkgConfirmPreimage sessionId matrixSeed pkBytes)

def rssZeroVec4 : PolyVec4 := fun _ => PolyTree.zero 8

def rssSumVec4List : List PolyVec4 → PolyVec4
  | [] => rssZeroVec4
  | v :: vsl => addVec4 v (rssSumVec4List vsl)

private theorem matVecMul4_rssZeroVec4 (A : PolyMat4) :
    matVecMul4 A rssZeroVec4 = rssZeroVec4 := by
  funext i
  dsimp only [matVecMul4, rssZeroVec4]
  have hMul0 : ∀ p : Poly256, negacyclicMul p (PolyTree.zero 8) = PolyTree.zero 8 :=
    LawfulCommRing.mul_zero
  simp only [hMul0, polyTree_add_zero]

private theorem addVec4_assoc (a b c : PolyVec4) :
    addVec4 (addVec4 a b) c = addVec4 a (addVec4 b c) := by
  funext i; exact polyTree_add_assoc (a i) (b i) (c i)

private theorem addVec4_comm (a b : PolyVec4) :
    addVec4 a b = addVec4 b a := by
  funext i; exact polyTree_add_comm (a i) (b i)

private theorem addVec4_rssZero_right (a : PolyVec4) :
    addVec4 a rssZeroVec4 = a := by
  funext i; exact polyTree_add_zero (a i)

private theorem addVec4_left_neg (a : PolyVec4) :
    addVec4 (negVec4 a) a = rssZeroVec4 := by
  funext i; exact polyTree_add_left_neg (a i)

private theorem subVec4_eq_add_neg (a b : PolyVec4) :
    subVec4 a b = addVec4 a (negVec4 b) := by
  funext i; exact polyTree_sub_eq_add_neg (a i) (b i)

private theorem matVecMul4_rssSumVec4List (A : PolyMat4) :
    ∀ (vsl : List PolyVec4),
      matVecMul4 A (rssSumVec4List vsl) = rssSumVec4List (vsl.map (matVecMul4 A))
  | [] => matVecMul4_rssZeroVec4 A
  | v :: vsl => by
    simp only [rssSumVec4List, List.map_cons, matVecMul4_add, matVecMul4_rssSumVec4List A vsl]

private theorem rssSumVec4List_add_zip :
    ∀ (xs ys : List PolyVec4),
      xs.length = ys.length →
      rssSumVec4List (List.zipWith addVec4 xs ys) = addVec4 (rssSumVec4List xs) (rssSumVec4List ys)
  | [], [], _ => by
    simp only [List.zipWith, rssSumVec4List, addVec4_rssZero_right]
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | x :: xs, y :: ys, h => by
    simp only [List.length_cons] at h
    have ih := rssSumVec4List_add_zip xs ys (Nat.succ.inj h)
    simp only [List.zipWith, rssSumVec4List, ih]
    rw [addVec4_assoc x y (addVec4 (rssSumVec4List xs) (rssSumVec4List ys)),
        ← addVec4_assoc y (rssSumVec4List xs) (rssSumVec4List ys),
        addVec4_comm y (rssSumVec4List xs),
        addVec4_assoc (rssSumVec4List xs) y (rssSumVec4List ys),
        ← addVec4_assoc x (rssSumVec4List xs) (addVec4 y (rssSumVec4List ys))]

/-- **`#tooth` (`tooth_uncommitted_dkg_rogue_key_forgery`)**:
    Without pre-opening share commitments and `"QSAG.TMLDSA.DKG.CONFIRM.V1"` transcript confirmation,
    a rushing adversary observing honest public contribution `t₀ : PolyVec4` chooses `t_bad := subVec4 tStar t₀`
    so the aggregate public vector `addVec4 t₀ t_bad` equals ANY target `tStar` (e.g. a known-trapdoor key)! -/
theorem tooth_uncommitted_dkg_rogue_key_forgery (t₀ tStar : PolyVec4) :
    addVec4 t₀ (subVec4 tStar t₀) = tStar := by
  rw [subVec4_eq_add_neg, addVec4_comm tStar (negVec4 t₀),
      ← addVec4_assoc t₀ (negVec4 t₀) tStar,
      addVec4_comm t₀ (negVec4 t₀), addVec4_left_neg,
      addVec4_comm rssZeroVec4 tStar, addVec4_rssZero_right]

/-- **Flagship §2.3 Theorem — `(t, m)` RSS Subset-Key Consistency & `"QSAG.TMLDSA.DKG.CONFIRM.V1"`
    Transcript Binding (`dkg_confirm_transcript_binding_and_rss_consistency`, `threshold_mldsa.rs:503-620`)**:
    1. **Honest-Holder Coverage & RSS Public-Key Homomorphism**: Whenever $1 \le t$ and $2t - 1 \le m$,
       every $(m - t + 1)$-subset $T$ has $\ge 1$ honest custodian outside any $(t - 1)$-corrupt coalition
       (`subset_honest_holder_exists`), AND summing subset public shares $t_T = A \cdot s_{1,T} + s_{2,T}$
       reconstructs the exact ML-DSA-44 key relation $t = A \cdot (\sum_T s_{1,T}) + (\sum_T s_{2,T})$.
    2. **`"QSAG.TMLDSA.DKG.CONFIRM.V1"` Equivocation / Mismatch Detection**: If all honest custodians check
       pairwise equality of `dkgConfirmDigest H sessionId matrixSeed pkBytes` (`threshold_mldsa.rs:581-600`),
       any disagreement on `(sessionId, matrixSeed, pkBytes)` (`< 256^8` bytes) either causes immediate DKG
       rejection or exhibits an explicit length-framed `cshake256_framed_32` collision under `H`! -/
theorem dkg_confirm_transcript_binding_and_rss_consistency
    (H : List UInt8 → List UInt8) :
    (∀ (t m : Nat) (subset corrupt : List Nat),
      1 ≤ t → 2 * t - 1 ≤ m →
      corrupt.length ≤ t - 1 →
      subset.Nodup → subset.length = m - t + 1 →
      ∃ h ∈ subset, h ∉ corrupt) ∧
    (∀ (A : PolyMat4) (s1Subs s2Subs : List PolyVec4),
      s1Subs.length = s2Subs.length →
      rssSumVec4List (List.zipWith (fun s1 s2 => addVec4 (matVecMul4 A s1) s2) s1Subs s2Subs) =
        addVec4 (matVecMul4 A (rssSumVec4List s1Subs)) (rssSumVec4List s2Subs)) ∧
    (∀ (sid₁ sid₂ mSeed₁ mSeed₂ pk₁ pk₂ : List UInt8),
      sid₁.length < 256 ^ 8 → sid₂.length < 256 ^ 8 →
      mSeed₁.length < 256 ^ 8 → mSeed₂.length < 256 ^ 8 →
      pk₁.length < 256 ^ 8 → pk₂.length < 256 ^ 8 →
      (sid₂, mSeed₂, pk₂) ≠ (sid₁, mSeed₁, pk₁) →
      dkgConfirmDigest H sid₁ mSeed₁ pk₁ ≠ dkgConfirmDigest H sid₂ mSeed₂ pk₂ ∨
        (dkgConfirmPreimage sid₁ mSeed₁ pk₁ ≠ dkgConfirmPreimage sid₂ mSeed₂ pk₂ ∧
         H (dkgConfirmPreimage sid₁ mSeed₁ pk₁) = H (dkgConfirmPreimage sid₂ mSeed₂ pk₂))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t m subset corrupt ht hm hCLen hSNd hSLen
    obtain ⟨h, _, hIn, hNotIn⟩ :=
      (subset_honest_holder_exists ht hm hCLen hSNd hSLen idMat4 0
        ⟨rssZeroVec4, rssZeroVec4, rssZeroVec4⟩).1
    exact ⟨h, hIn, hNotIn⟩
  · intro A s1Subs s2Subs hLen
    have hZipEq :
        List.zipWith (fun s1 s2 => addVec4 (matVecMul4 A s1) s2) s1Subs s2Subs =
          List.zipWith addVec4 (s1Subs.map (matVecMul4 A)) s2Subs := by
      induction s1Subs generalizing s2Subs with
      | nil => cases s2Subs <;> rfl
      | cons x xs ih =>
        cases s2Subs with
        | nil => cases hLen
        | cons y ys =>
          simp only [List.length_cons] at hLen
          simp only [List.zipWith, List.map_cons, ih ys (Nat.succ.inj hLen)]
    rw [hZipEq, rssSumVec4List_add_zip _ _ (by rw [List.length_map, hLen]), ← matVecMul4_rssSumVec4List]
  · intro sid₁ sid₂ mSeed₁ mSeed₂ pk₁ pk₂ hs1 hs2 hm1 hm2 hp1 hp2 hNe
    if hDigEq : dkgConfirmDigest H sid₁ mSeed₁ pk₁ = dkgConfirmDigest H sid₂ mSeed₂ pk₂ then
      right
      refine ⟨?_, hDigEq⟩
      intro hPreEq
      unfold dkgConfirmPreimage at hPreEq
      have hAll1 : ∀ f ∈ [sid₁, mSeed₁, pk₁], f.length < 256 ^ 8 := by
        intro f hf
        rcases List.mem_cons.mp hf with rfl | h1
        · exact hs1
        · rcases List.mem_cons.mp h1 with rfl | h2
          · exact hm1
          · rcases List.mem_cons.mp h2 with rfl | h3
            · exact hp1
            · cases h3
      have hAll2 : ∀ g ∈ [sid₂, mSeed₂, pk₂], g.length < 256 ^ 8 := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | h1
        · exact hs2
        · rcases List.mem_cons.mp h1 with rfl | h2
          · exact hm2
          · rcases List.mem_cons.mp h2 with rfl | h3
            · exact hp2
            · cases h3
      have hFrEq := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hPreEq
      injection hFrEq with eSid t1
      injection t1 with eSeed t2
      injection t2 with ePk _
      exact hNe (by rw [eSid, eSeed, ePk])
    else
      exact Or.inl hDigEq

/-! ### §2.4 Aggregate Rejection-Barrier Zero-Leakage, `u_com` Binding & Standalone FIPS 204 `mldsaVerify` (`P0-06`) -/

/-- **`#tooth` (`premature_z_release_leaks_s2_boundary`)**:
    If `z = y + c * s1` is prematurely released on an aborted signing attempt where
    `mldsa44Gamma2 - mldsa44Beta ≤ lowBitsNormVec4 (w - c * s2)`, ANY observer holding only public
    `(A, t = A*s1 + s2, c, z)` computes `A * z - c * t = w - c * s2` identically and directly observes
    the secret-dependent `s2` boundary alignment `γ₂ - β ≤ ‖LowBits(w - c * s2)‖_∞`! -/
theorem premature_z_release_leaks_s2_boundary
    (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256)
    (hBoundaryAbort :
      mldsa44Gamma2 - mldsa44Beta ≤ lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2))) :
    let t := addVec4 (matVecMul4 A s1) s2
    let w := matVecMul4 A y
    let z := addVec4 y (mulPolyVec4 c s1)
    let publicRecovered := subVec4 (matVecMul4 A z) (mulPolyVec4 c t)
    publicRecovered = subVec4 w (mulPolyVec4 c s2) ∧
    mldsa44Gamma2 - mldsa44Beta ≤ lowBitsNormVec4 publicRecovered := by
  intro t w z publicRecovered
  have hRecover : publicRecovered = subVec4 w (mulPolyVec4 c s2) := by
    dsimp only [publicRecovered, z, w, t]
    rw [matVecMul4_add, matVecMul4_mulPoly]
    funext i
    dsimp only [addVec4, subVec4, mulPolyVec4]
    rw [negacyclicMul_left_distrib]
    let wy := matVecMul4 A y i
    let u1 := negacyclicMul c (matVecMul4 A s1 i)
    let u2 := negacyclicMul c (s2 i)
    change PolyTree.sub (PolyTree.add wy u1) (PolyTree.add u1 u2) = PolyTree.sub wy u2
    apply poly256_add_left_cancel (a := PolyTree.add u1 u2)
    have hL :
        PolyTree.add (PolyTree.add u1 u2) (PolyTree.sub (PolyTree.add wy u1) (PolyTree.add u1 u2)) =
          PolyTree.add wy u1 := by
      rw [polyTree_sub_eq_add_neg,
          polyTree_add_comm (PolyTree.add wy u1) (PolyTree.neg (PolyTree.add u1 u2)),
          ← polyTree_add_assoc (PolyTree.add u1 u2) (PolyTree.neg (PolyTree.add u1 u2)) (PolyTree.add wy u1),
          polyTree_add_comm (PolyTree.add u1 u2) (PolyTree.neg (PolyTree.add u1 u2)),
          polyTree_add_left_neg, polyTree_add_comm (PolyTree.zero 8), polyTree_add_zero]
    have hR :
        PolyTree.add (PolyTree.add u1 u2) (PolyTree.sub wy u2) = PolyTree.add wy u1 := by
      rw [polyTree_sub_eq_add_neg, polyTree_add_comm wy (PolyTree.neg u2),
          polyTree_add_assoc u1 u2 (PolyTree.add (PolyTree.neg u2) wy),
          ← polyTree_add_assoc u2 (PolyTree.neg u2) wy,
          polyTree_add_comm u2 (PolyTree.neg u2), polyTree_add_left_neg,
          polyTree_add_comm (PolyTree.zero 8) wy, polyTree_add_zero,
          polyTree_add_comm u1 wy]
    exact hL.trans hR.symm
  exact ⟨hRecover, hRecover.symm ▸ hBoundaryAbort⟩

/-- A boundary abort with genuinely nonzero secret vectors, tied to the leakage experiment. -/
theorem premature_z_release_leaks_s2_boundary_inhabited :
    ∃ (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256),
      s1 ≠ (fun _ => PolyTree.zero 8) ∧
      s2 ≠ (fun _ => PolyTree.zero 8) ∧
      c ≠ PolyTree.zero 8 ∧
      mldsa44Gamma2 - mldsa44Beta ≤ lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2)) ∧
      subVec4 (matVecMul4 A (addVec4 y (mulPolyVec4 c s1)))
        (mulPolyVec4 c (addVec4 (matVecMul4 A s1) s2)) =
        subVec4 (matVecMul4 A y) (mulPolyVec4 c s2) := by
  let v1 : PolyVec4 := fun _ => polyTreeConstLeaf 8 Fq204.one
  let yHi : PolyVec4 := fun _ => polyTreeConstLeaf 8 ⟨95201, by decide⟩
  have hn : v1 ≠ (fun _ => PolyTree.zero 8) := by
    intro h
    have he := congrFun h (0 : Fin 4)
    have hv := congrArg PolyTree.infNorm he
    simp only [v1, polyTreeConstLeaf_infNorm] at hv
    change 1 = 0 at hv
    omega
  have hb : mldsa44Gamma2 - mldsa44Beta ≤
      lowBitsNormVec4 (subVec4 (matVecMul4 idMat4 yHi)
        (mulPolyVec4 (PolyTree.constUnit 8) v1)) := by
    rw [matVecMul4_idMat4]
    have hm : mulPolyVec4 (PolyTree.constUnit 8) v1 = v1 := by
      funext i; exact negacyclicMul_one_left (v1 i)
    rw [hm]
    unfold lowBitsNormVec4 subVec4
    dsimp only [yHi, v1]
    simp only [polyTree_sub_eq_add_neg, polyTreeConstLeaf_neg,
      polyTreeConstLeaf_add, polyTreeConstLeaf_lowBitsNorm, Nat.max_self]
    decide
  exact ⟨idMat4, v1, v1, yHi, PolyTree.constUnit 8, hn, hn, by decide, hb,
    (premature_z_release_leaks_s2_boundary idMat4 v1 v1 yHi (PolyTree.constUnit 8) hb).1⟩

/-- Tree-lifted centered residual norm `‖(r - w1 * 2γ₂) mod± q‖_∞` (`threshold_mldsa.rs:789-799`). -/
def centeredDiffNormTree : {d : Nat} → PolyTree d → NatTree d → Nat
  | 0, .leaf r, .leaf w1 => Fq204.centeredAbs (Fq204.sub r (Fq204.ofNat (w1 * 190464)))
  | _ + 1, .branch r0 r1, .branch w0 w1 =>
    max (centeredDiffNormTree r0 w0) (centeredDiffNormTree r1 w1)

private theorem polyTreeConstLeaf_centeredDiffNorm (r w : Fq204) : ∀ (d : Nat),
    centeredDiffNormTree (polyTreeConstLeaf d r) (highBitsTree (polyTreeConstLeaf d w)) =
      Fq204.centeredAbs (Fq204.sub r (Fq204.ofNat ((mldsaHighBits w) * 190464)))
  | 0 => rfl
  | d + 1 => by
    simp only [polyTreeConstLeaf, highBitsTree, centeredDiffNormTree,
      polyTreeConstLeaf_centeredDiffNorm r w d, Nat.max_self]

def natTreeAllLt44 : {d : Nat} → NatTree d → Prop
  | 0, .leaf w1 => w1 < 44
  | _ + 1, .branch w0 w1 => natTreeAllLt44 w0 ∧ natTreeAllLt44 w1

theorem highBitsTree_allLt44 : ∀ {d : Nat} (p : PolyTree d), natTreeAllLt44 (highBitsTree p)
  | 0, .leaf r => (decompose_reconstruct r).1
  | _ + 1, .branch p0 p1 => And.intro (highBitsTree_allLt44 p0) (highBitsTree_allLt44 p1)

theorem centeredDiffNormTree_lt_iff : ∀ {d : Nat} (r : PolyTree d) (w1 : NatTree d) {B : Nat},
    natTreeAllLt44 w1 → B ≤ 95232 →
    (centeredDiffNormTree r w1 < B ↔ lowBitsNormTree r < B ∧ highBitsTree r = w1)
  | 0, .leaf r, .leaf w1, B, hw1, hB => by
    simp only [centeredDiffNormTree, lowBitsNormTree, highBitsTree, NatTree.leaf.injEq]
    exact centered_diff_lt_iff_lowBits_and_highBits r hw1 hB
  | _ + 1, .branch r0 r1, .branch w0 w1, B, hw, hB => by
    rcases hw with ⟨hw0, hw1⟩
    simp only [centeredDiffNormTree, lowBitsNormTree, highBitsTree, NatTree.branch.injEq]
    have ih0 := centeredDiffNormTree_lt_iff r0 w0 hw0 hB
    have ih1 := centeredDiffNormTree_lt_iff r1 w1 hw1 hB
    constructor
    · intro hLt
      have h0 : centeredDiffNormTree r0 w0 < B := by omega
      have h1 : centeredDiffNormTree r1 w1 < B := by omega
      obtain ⟨l0, e0⟩ := ih0.mp h0
      obtain ⟨l1, e1⟩ := ih1.mp h1
      exact ⟨by omega, e0, e1⟩
    · rintro ⟨hLow, e0, e1⟩
      have h0 : centeredDiffNormTree r0 w0 < B := ih0.mpr ⟨by omega, e0⟩
      have h1 : centeredDiffNormTree r1 w1 < B := ih1.mpr ⟨by omega, e1⟩
      omega

def centeredDiffNormVec4 (r : PolyVec4) (w1 : Fin 4 → NatTree 8) : Nat :=
  max (max (centeredDiffNormTree (r ⟨0, by decide⟩) (w1 ⟨0, by decide⟩))
           (centeredDiffNormTree (r ⟨1, by decide⟩) (w1 ⟨1, by decide⟩)))
      (max (centeredDiffNormTree (r ⟨2, by decide⟩) (w1 ⟨2, by decide⟩))
           (centeredDiffNormTree (r ⟨3, by decide⟩) (w1 ⟨3, by decide⟩)))

theorem centeredDiffNormVec4_lt_iff (r w : PolyVec4) {B : Nat} (hB : B ≤ 95232) :
    centeredDiffNormVec4 r (highBitsVec4 w) < B ↔
      lowBitsNormVec4 r < B ∧ highBitsVec4 r = highBitsVec4 w := by
  unfold centeredDiffNormVec4 lowBitsNormVec4
  have ih0 := centeredDiffNormTree_lt_iff (r ⟨0, by decide⟩) (highBitsTree (w ⟨0, by decide⟩))
    (highBitsTree_allLt44 _) hB
  have ih1 := centeredDiffNormTree_lt_iff (r ⟨1, by decide⟩) (highBitsTree (w ⟨1, by decide⟩))
    (highBitsTree_allLt44 _) hB
  have ih2 := centeredDiffNormTree_lt_iff (r ⟨2, by decide⟩) (highBitsTree (w ⟨2, by decide⟩))
    (highBitsTree_allLt44 _) hB
  have ih3 := centeredDiffNormTree_lt_iff (r ⟨3, by decide⟩) (highBitsTree (w ⟨3, by decide⟩))
    (highBitsTree_allLt44 _) hB
  dsimp only [highBitsVec4]
  constructor
  · intro hLt
    obtain ⟨l0, e0⟩ := ih0.mp (by omega)
    obtain ⟨l1, e1⟩ := ih1.mp (by omega)
    obtain ⟨l2, e2⟩ := ih2.mp (by omega)
    obtain ⟨l3, e3⟩ := ih3.mp (by omega)
    refine ⟨by omega, ?_⟩
    funext i
    rcases i with ⟨idx, hidx⟩
    have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hCases with rfl | rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  · rintro ⟨hLow, hEq⟩
    have e0 := congrFun hEq ⟨0, by decide⟩
    have e1 := congrFun hEq ⟨1, by decide⟩
    have e2 := congrFun hEq ⟨2, by decide⟩
    have e3 := congrFun hEq ⟨3, by decide⟩
    have c0 := ih0.mpr ⟨by omega, e0⟩
    have c1 := ih1.mpr ⟨by omega, e1⟩
    have c2 := ih2.mpr ⟨by omega, e2⟩
    have c3 := ih3.mpr ⟨by omega, e3⟩
    omega

/-- Parameterized ML-DSA-44 algebraic verification core (legacy MIR bridge API):
    Checks `‖z‖_∞ < γ₁ - β`, `weight(h) ≤ ω`, and `c_tilde = H(μ, UseHint(h, A*z - c*t1*2^d))`. -/
@[expose] def mldsaVerify
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (t1Scaled : PolyVec4) (mu : List UInt8)
    (cTilde : List UInt8) (z : PolyVec4) (h : Fin 4 → HintTree 8) : Bool :=
  let c := sampleInBall cTilde
  let w1Prime := useHintVec4 h (subVec4 (matVecMul4 A z) (mulPolyVec4 c t1Scaled))
  decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
  decide (hintWeightVec4 h ≤ mldsa44Omega) &&
  decide (cTilde = chalHash mu w1Prime)

/-- Persistent custodian state for `(t, m)` RSS `threshold_sign_mldsa_party` (`threshold_mldsa.rs:772-1055`):
    holds current signing `epoch`, monotonic `nextAttempt` burn counter, matrix `A`, and RSS subset
    key vectors `(s1Subsets, s2Subsets)` for the aggregate reference computation. -/
structure RssMlDsaSignerState where
  epoch : Nat
  nextAttempt : Nat
  A : PolyMat4
  s1Subsets : List PolyVec4
  s2Subsets : List PolyVec4

/-- Supplied multiplication outputs consumed by the signing transition. These are checked
    against the operands, rather than accepting a caller's success flag. This is an exact
    aggregate checker; a private distributed sacrifice implementation needs a separate refinement. -/
structure RssSignProducts where
  w : PolyVec4
  cs1 : PolyVec4
  cs2 : PolyVec4
  ct0 : PolyVec4

def rssComputeProducts
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (mu : List UInt8) (ySubsets : List PolyVec4) : RssSignProducts :=
  let s1 := rssSumVec4List st.s1Subsets
  let s2 := rssSumVec4List st.s2Subsets
  let w := matVecMul4 st.A (rssSumVec4List ySubsets)
  let c := sampleInBall (chalHash mu (highBitsVec4 w))
  { w := w, cs1 := mulPolyVec4 c s1, cs2 := mulPolyVec4 c s2,
    ct0 := mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2)) }

/-- Single RSS signing-attempt input (`threshold_mldsa.rs:795-975`):
    binds `(epoch, sessionId, attempt)`, message representative `mu`, RSS nonce shares `ySubsets`,
    caller-provided masks `(maskW, maskZ, maskLow)`, and raw multiplication outputs. -/
structure RssMlDsaAttemptInput where
  epoch : Nat
  sessionId : List UInt8
  attempt : Nat
  mu : List UInt8
  ySubsets : List PolyVec4
  maskW : PolyVec4
  maskZ : PolyVec4
  maskLow : PolyVec4
  products : RssSignProducts

def rssProductsValid
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) : Bool :=
  let expected := rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets
  polyVec4EqBool inp.products.w expected.w &&
  polyVec4EqBool inp.products.cs1 expected.cs1 &&
  polyVec4EqBool inp.products.cs2 expected.cs2 &&
  polyVec4EqBool inp.products.ct0 expected.ct0

theorem rssProductsValid_eq_true_iff
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    rssProductsValid chalHash sampleInBall st inp = true ↔
      inp.products = rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets := by
  simp only [rssProductsValid, Bool.and_eq_true, polyVec4EqBool_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨hw, hs1⟩, hs2⟩, ht⟩
    revert hw hs1 hs2 ht
    generalize rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets = expected
    generalize inp.products = supplied
    cases supplied
    cases expected
    intro hw hs1 hs2 ht
    simp_all
  · intro h
    rw [h]
    exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩

/-- Emitted standalone FIPS 204 signature + burned attempt counter. -/
structure ThresholdSignSig where
  cTilde : List UInt8
  z : PolyVec4
  h : Fin 4 → HintTree 8
  usedAttempt : Nat

/-- Exact public transcript opened during a `threshold_sign_mldsa_party` attempt (`threshold_mldsa.rs:940-1015`):
    even when `rejectBit = true` (unmasked `(z, h)` suppressed!), the protocol publicly opens the `< q`-masked
    vectors `(openedMaskedW, openedMaskedZ, openedMaskedLow)`, rounded `openedW1 = HighBits(w)`, and `rejectBit`. -/
structure RssSignPublicAbortView where
  openedMaskedW : PolyVec4
  openedW1 : Fin 4 → NatTree 8
  openedMaskedZ : PolyVec4
  openedMaskedLow : PolyVec4
  rejectBit : Bool
  usedAttempt : Nat

/-- Pre-open gate abort reasons (prior to opening `RssSignPublicAbortView`). -/
inductive RssPreOpenAbortReason where
  | attemptReplay
  | mpcSacrificeFailed
  deriving DecidableEq, Repr

/-- Constructive `< q` additive mask bijection `m ↦ addVec4 target m` on `PolyVec4` (`rss_mpc.rs`). -/
def rssMaskAddEquiv (target : PolyVec4) : SimpleEquiv PolyVec4 PolyVec4 where
  toFun m := addVec4 target m
  invFun v := subVec4 v target
  left_inv m := by
    rw [subVec4_eq_add_neg, addVec4_comm target m,
        addVec4_assoc m target (negVec4 target),
        addVec4_comm target (negVec4 target), addVec4_left_neg, addVec4_rssZero_right]
  right_inv v := by
    rw [subVec4_eq_add_neg, addVec4_comm v (negVec4 target),
        ← addVec4_assoc target (negVec4 target) v,
        addVec4_comm target (negVec4 target), addVec4_left_neg,
        addVec4_comm rssZeroVec4 v, addVec4_rssZero_right]

private def seRefl (α : Type) : SimpleEquiv α α where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

private def seSymm {α β : Type} (e : SimpleEquiv α β) : SimpleEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

private def seTrans {α β γ : Type} (e₁ : SimpleEquiv α β) (e₂ : SimpleEquiv β γ) : SimpleEquiv α γ where
  toFun x := e₂.toFun (e₁.toFun x)
  invFun z := e₁.invFun (e₂.invFun z)
  left_inv x := by rw [e₂.left_inv, e₁.left_inv]
  right_inv z := by rw [e₁.right_inv, e₂.right_inv]

private def seProdCongr {α₁ α₂ β₁ β₂ : Type}
    (eA : SimpleEquiv α₁ α₂) (eB : SimpleEquiv β₁ β₂) :
    SimpleEquiv (α₁ × β₁) (α₂ × β₂) where
  toFun p := (eA.toFun p.1, eB.toFun p.2)
  invFun q := (eA.invFun q.1, eB.invFun q.2)
  left_inv := fun ⟨a, b⟩ => by dsimp only; rw [eA.left_inv a, eB.left_inv b]
  right_inv := fun ⟨c, d⟩ => by dsimp only; rw [eA.right_inv c, eB.right_inv d]

private def sePiCongrRight {ι : Type} {α β : ι → Type}
    (es : ∀ i, SimpleEquiv (α i) (β i)) :
    SimpleEquiv (∀ i, α i) (∀ i, β i) where
  toFun f i := (es i).toFun (f i)
  invFun g i := (es i).invFun (g i)
  left_inv f := funext fun i => (es i).left_inv (f i)
  right_inv g := funext fun i => (es i).right_inv (g i)

private def seDepProd {α₁ α₂ β₁ β₂ : Type}
    (eqA : SimpleEquiv α₁ α₂)
    (eqB : α₁ → SimpleEquiv β₁ β₂) :
    SimpleEquiv (α₁ × β₁) (α₂ × β₂) where
  toFun p := (eqA.toFun p.1, (eqB p.1).toFun p.2)
  invFun q :=
    let a := eqA.invFun q.1
    (a, (eqB a).invFun q.2)
  left_inv := fun ⟨a, b⟩ => by
    dsimp only
    rw [eqA.left_inv a, (eqB a).left_inv b]
  right_inv := fun ⟨c, d⟩ => by
    dsimp only
    rw [eqA.right_inv c, (eqB (eqA.invFun c)).right_inv d]

/-- Triple `< q` RSS mask bijection over `(maskW, maskZ, maskLow)`. -/
def rssMaskTripleEquiv (w z u : PolyVec4) :
    SimpleEquiv (PolyVec4 × PolyVec4 × PolyVec4) (PolyVec4 × PolyVec4 × PolyVec4) :=
  seProdCongr (rssMaskAddEquiv w)
    (seProdCongr (rssMaskAddEquiv z) (rssMaskAddEquiv u))

/-- Explicit leakage-parameterized abort simulator (`threshold_mldsa.rs:940-1015`):
    given **only** the public ideal abort leakage `(leakedW1, rejectBit := true, usedAttempt)` and uniform
    simulator masks `simMasks` (zero secret shares `s1Subsets, s2Subsets, ySubsets`!), constructs the corresponding
    `RssSignPublicAbortView`. Equality of distributions additionally requires independent uniform masks. -/
def rssAbortSimulator
    (leakedW1 : Fin 4 → NatTree 8) (usedAttempt : Nat)
    (simMasks : PolyVec4 × PolyVec4 × PolyVec4) : RssSignPublicAbortView :=
  { openedMaskedW := simMasks.1
    openedW1 := leakedW1
    openedMaskedZ := simMasks.2.1
    openedMaskedLow := simMasks.2.2
    rejectBit := true
    usedAttempt := usedAttempt }

private def mkRssSignAttemptOutcome
    (stBurned : RssMlDsaSignerState) (usedAttempt : Nat)
    (cTilde : List UInt8) (w z u maskW maskZ maskLow : PolyVec4)
    (w1 : Fin 4 → NatTree 8) (h : Fin 4 → HintTree 8) (accept : Bool) :
    StepOutcome RssMlDsaSignerState
      (RssSignPublicAbortView × Option ThresholdSignSig)
      RssPreOpenAbortReason :=
  let publicView : RssSignPublicAbortView :=
    { openedMaskedW := addVec4 w maskW
      openedW1 := w1
      openedMaskedZ := addVec4 z maskZ
      openedMaskedLow := addVec4 u maskLow
      rejectBit := !accept
      usedAttempt := usedAttempt }
  match accept with
  | true =>
    .ok stBurned (publicView, some { cTilde := cTilde, z := z, h := h, usedAttempt := usedAttempt })
  | false =>
    .ok stBurned (publicView, none)

private theorem mkRssSignAttemptOutcome_ne_err
    {stBurned st' : RssMlDsaSignerState} {usedAttempt : Nat}
    {cTilde : List UInt8} {w z u maskW maskZ maskLow : PolyVec4}
    {w1 : Fin 4 → NatTree 8} {h : Fin 4 → HintTree 8} {accept : Bool}
    {err : RssPreOpenAbortReason} :
    mkRssSignAttemptOutcome stBurned usedAttempt cTilde w z u maskW maskZ maskLow w1 h accept ≠
      .err st' err := by
  unfold mkRssSignAttemptOutcome
  cases accept <;> intro hc <;> cases hc

private theorem mkRssSignAttemptOutcome_eq_ok
    {stBurned st' : RssMlDsaSignerState} {usedAttempt : Nat}
    {cTilde : List UInt8} {w z u maskW maskZ maskLow : PolyVec4}
    {w1 : Fin 4 → NatTree 8} {h : Fin 4 → HintTree 8} {accept : Bool}
    {pubView : RssSignPublicAbortView} {mSig : Option ThresholdSignSig}
    (hOk : mkRssSignAttemptOutcome stBurned usedAttempt cTilde w z u maskW maskZ maskLow w1 h accept =
           .ok st' (pubView, mSig)) :
    st' = stBurned ∧
    pubView = { openedMaskedW := addVec4 w maskW, openedW1 := w1,
                openedMaskedZ := addVec4 z maskZ, openedMaskedLow := addVec4 u maskLow,
                rejectBit := !accept, usedAttempt := usedAttempt } ∧
    ((accept = true ∧ mSig = some { cTilde := cTilde, z := z, h := h, usedAttempt := usedAttempt }) ∨
     (accept = false ∧ mSig = none)) := by
  unfold mkRssSignAttemptOutcome at hOk
  cases accept with
  | true =>
    injection hOk with hSt hPair
    injection hPair with hPub hSig
    exact ⟨hSt.symm, hPub.symm, Or.inl ⟨rfl, hSig.symm⟩⟩
  | false =>
    injection hOk with hSt hPair
    injection hPair with hPub hSig
    exact ⟨hSt.symm, hPub.symm, Or.inr ⟨rfl, hSig.symm⟩⟩

private theorem mkRssSignAttemptOutcome_true
    (stBurned : RssMlDsaSignerState) (usedAttempt : Nat)
    (cTilde : List UInt8) (w z u maskW maskZ maskLow : PolyVec4)
    (w1 : Fin 4 → NatTree 8) (h : Fin 4 → HintTree 8) {accept : Bool}
    (hAcc : accept = true) :
    mkRssSignAttemptOutcome stBurned usedAttempt cTilde w z u maskW maskZ maskLow w1 h accept =
      .ok stBurned
        ({ openedMaskedW := addVec4 w maskW, openedW1 := w1,
           openedMaskedZ := addVec4 z maskZ, openedMaskedLow := addVec4 u maskLow,
           rejectBit := false, usedAttempt := usedAttempt },
         some { cTilde := cTilde, z := z, h := h, usedAttempt := usedAttempt }) := by
  subst hAcc
  rfl

private theorem mkRssSignAttemptOutcome_false
    (stBurned : RssMlDsaSignerState) (usedAttempt : Nat)
    (cTilde : List UInt8) (w z u maskW maskZ maskLow : PolyVec4)
    (w1 : Fin 4 → NatTree 8) (h : Fin 4 → HintTree 8) {accept : Bool}
    (hAcc : accept = false) :
    mkRssSignAttemptOutcome stBurned usedAttempt cTilde w z u maskW maskZ maskLow w1 h accept =
      .ok stBurned
        ({ openedMaskedW := addVec4 w maskW, openedW1 := w1,
           openedMaskedZ := addVec4 z maskZ, openedMaskedLow := addVec4 u maskLow,
           rejectBit := true, usedAttempt := usedAttempt },
         none) := by
  subst hAcc
  rfl

/-- Signing computation on products that have already been checked: response, hint and the
    rejection predicate. Shared by the exact-product reference transition and by the
    sacrifice-gated transition. -/
def rssSignCore
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (stBurned : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    StepOutcome RssMlDsaSignerState
      (RssSignPublicAbortView × Option ThresholdSignSig)
      RssPreOpenAbortReason :=
  let y := rssSumVec4List inp.ySubsets
  let w := inp.products.w
  let w1 := highBitsVec4 w
  let cTilde := chalHash inp.mu w1
  let ct0 := inp.products.ct0
  let z := addVec4 y inp.products.cs1
  let u := subVec4 w inp.products.cs2
  let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
  let accept : Bool :=
    decide (infNormVec4 ct0 < mldsa44Gamma2) &&
    decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
    decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
    decide (hintWeightVec4 h ≤ mldsa44Omega)
  mkRssSignAttemptOutcome stBurned inp.attempt cTilde w z u
    inp.maskW inp.maskZ inp.maskLow w1 h accept

/-- Per-attempt RSS transition of `threshold_sign_mldsa_party` (`threshold_mldsa.rs:795-1055`):
    - Enforces `(inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt)` and immediately burns
      `nextAttempt := st.nextAttempt + 1` BEFORE Phase 1;
    - Requires `rssProductsValid chalHash sampleInBall st inp = true` (exact aggregate product validation);
    - Evaluates `w1 = HighBits(w)`, `c = SampleInBall(H(μ, w1))`, and the RSS rejection predicate
      `accept`;
    - On rejection (`accept = false`), emits `(publicView, none)` (`rejectBit = true`, no separate unmasked `z` field);
    - On acceptance (`accept = true`), emits `(publicView, some sig)` (`rejectBit = false`). -/
def rssThresholdSignStep
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    StepOutcome RssMlDsaSignerState
      (RssSignPublicAbortView × Option ThresholdSignSig)
      RssPreOpenAbortReason :=
  match decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
  | false => .err st .attemptReplay
  | true =>
    let stBurned : RssMlDsaSignerState := { st with nextAttempt := st.nextAttempt + 1 }
    match rssProductsValid chalHash sampleInBall st inp with
    | false => .err stBurned .mpcSacrificeFailed
    | true => rssSignCore chalHash stBurned inp

/-- Canonical `SimulationSpine.PartyMachine` instantiation of `rssThresholdSignStep`. -/
def rssThresholdSignMachine
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    PartyMachine RssMlDsaSignerState RssMlDsaAttemptInput
      (RssSignPublicAbortView × Option ThresholdSignSig) :=
  PartyMachine.ofOutcome (rssThresholdSignStep chalHash sampleInBall)

/-- An attempt that passes the replay check, carries the exact products and satisfies the
    rejection predicate is accepted: the machine burns the attempt and releases the signature.
    Stated over arbitrary `st` and `inp`, so a concrete witness applies it instead of unfolding
    the transition on concrete polynomials. -/
theorem rssThresholdSignMachine_step_accept
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (hEpoch : inp.epoch = st.epoch) (hAttempt : inp.attempt = st.nextAttempt)
    (hProducts : inp.products = rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets) :
    let s1 := rssSumVec4List st.s1Subsets
    let s2 := rssSumVec4List st.s2Subsets
    let y := rssSumVec4List inp.ySubsets
    let t0 := power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2)
    let w := matVecMul4 st.A y
    let w1 := highBitsVec4 w
    let cTilde := chalHash inp.mu w1
    let c := sampleInBall cTilde
    let ct0 := mulPolyVec4 c t0
    let z := addVec4 y (mulPolyVec4 c s1)
    let u := subVec4 w (mulPolyVec4 c s2)
    let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
    (decide (infNormVec4 ct0 < mldsa44Gamma2) &&
     decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
     decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
     decide (hintWeightVec4 h ≤ mldsa44Omega)) = true →
    (rssThresholdSignMachine chalHash sampleInBall).step st inp =
      some ({ st with nextAttempt := st.nextAttempt + 1 },
        ({ openedMaskedW := addVec4 w inp.maskW,
           openedW1 := w1,
           openedMaskedZ := addVec4 z inp.maskZ,
           openedMaskedLow := addVec4 u inp.maskLow,
           rejectBit := false,
           usedAttempt := inp.attempt },
         some { cTilde := cTilde, z := z, h := h, usedAttempt := inp.attempt })) := by
  intro s1 s2 y t0 w w1 cTilde c ct0 z u h hAccept
  have hRun : rssThresholdSignStep chalHash sampleInBall st inp =
      .ok { st with nextAttempt := st.nextAttempt + 1 }
        ({ openedMaskedW := addVec4 w inp.maskW,
           openedW1 := w1,
           openedMaskedZ := addVec4 z inp.maskZ,
           openedMaskedLow := addVec4 u inp.maskLow,
           rejectBit := false,
           usedAttempt := inp.attempt },
         some { cTilde := cTilde, z := z, h := h, usedAttempt := inp.attempt }) := by
    unfold rssThresholdSignStep rssSignCore
    rw [decide_eq_true (⟨hEpoch, hAttempt⟩ : inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt)]
    rw [(rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mpr hProducts]
    rw [hProducts]
    dsimp only [rssComputeProducts]
    exact mkRssSignAttemptOutcome_true
      { st with nextAttempt := st.nextAttempt + 1 } inp.attempt
      cTilde w z u inp.maskW inp.maskZ inp.maskLow w1 h hAccept
  dsimp only [rssThresholdSignMachine, PartyMachine.ofOutcome]
  rw [hRun]

private theorem rssThresholdSignStep_ok_meta
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {st st' : RssMlDsaSignerState} {inp : RssMlDsaAttemptInput}
    {pubView : RssSignPublicAbortView} {mSig : Option ThresholdSignSig}
    (hOk : rssThresholdSignStep chalHash sampleInBall st inp = .ok st' (pubView, mSig)) :
    inp.epoch = st.epoch ∧
    inp.attempt = st.nextAttempt ∧
    st'.epoch = st.epoch ∧
    st'.nextAttempt = st.nextAttempt + 1 ∧
    pubView.usedAttempt = st.nextAttempt ∧
    (∀ sig, mSig = some sig →
      pubView.rejectBit = false ∧
      sig.usedAttempt = st.nextAttempt ∧
      mldsaVerify chalHash sampleInBall st.A
        (power2RoundHighVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))
        inp.mu sig.cTilde sig.z sig.h = true) := by
  unfold rssThresholdSignStep rssSignCore at hOk
  cases hGate : decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
  | false => rw [hGate] at hOk; cases hOk
  | true =>
    rw [hGate] at hOk
    obtain ⟨hEp, hAtt⟩ := of_decide_eq_true hGate
    cases hSac : rssProductsValid chalHash sampleInBall st inp with
    | false => rw [hSac] at hOk; cases hOk
    | true =>
      rw [hSac] at hOk
      rw [(rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp hSac] at hOk
      dsimp only [rssComputeProducts] at hOk
      obtain ⟨hSt, hPub, hBranch⟩ := mkRssSignAttemptOutcome_eq_ok hOk
      subst hSt hPub
      refine ⟨hEp, hAtt, rfl, rfl, hAtt, ?_⟩
      intro sig hSome
      rcases hBranch with ⟨hAcc, hSigEq⟩ | ⟨_, hNone⟩
      · rw [hSigEq] at hSome
        injection hSome with hSig
        subst hSig
        rw [hAcc]
        dsimp only [Bool.not_true]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hAcc
        rcases hAcc with ⟨⟨⟨hCt0Lt, hzLt⟩, hDiffLt⟩, hWeightLe⟩
        have hB : mldsa44Gamma2 - mldsa44Beta ≤ 95232 := by decide
        obtain ⟨hLowLt, hHighEq⟩ := (centeredDiffNormVec4_lt_iff _ _ hB).mp hDiffLt
        refine ⟨rfl, hAtt, ?_⟩
        unfold mldsaVerify
        dsimp only
        have hUseHint := highBits_az_sub_ct_eq_w1 st.A
          (rssSumVec4List st.s1Subsets) (rssSumVec4List st.s2Subsets)
          (rssSumVec4List inp.ySubsets)
          (sampleInBall (chalHash inp.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
          mldsa44Beta hLowLt hCt0Lt
        dsimp only at hUseHint
        rw [hUseHint, hHighEq]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hzLt, hWeightLe⟩, trivial⟩
      · rw [hNone] at hSome
        cases hSome

private theorem rssThresholdSignStep_err_attempt
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    let nextSt := (rssThresholdSignMachine chalHash sampleInBall).errStep st inp
    st.nextAttempt ≤ nextSt.nextAttempt ∧
    ((inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) →
      nextSt.nextAttempt = st.nextAttempt + 1) := by
  dsimp only [rssThresholdSignMachine, PartyMachine.ofOutcome]
  cases hOut : rssThresholdSignStep chalHash sampleInBall st inp with
  | ok st' outPair =>
    rcases outPair with ⟨pubView, mSig⟩
    obtain ⟨_, _, _, hNext, _⟩ := rssThresholdSignStep_ok_meta hOut
    dsimp only
    exact ⟨by omega, fun _ => hNext⟩
  | err st' _ =>
    dsimp only
    unfold rssThresholdSignStep rssSignCore at hOut
    cases hGate : decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
    | false =>
      rw [hGate] at hOut
      injection hOut with hSt _
      subst hSt
      exact ⟨Nat.le_refl _, fun hg => by rw [decide_eq_true hg] at hGate; cases hGate⟩
    | true =>
      rw [hGate] at hOut
      cases hSac : rssProductsValid chalHash sampleInBall st inp with
      | false =>
        rw [hSac] at hOut
        injection hOut with hSt _
        subst hSt
        exact ⟨by dsimp only; omega, fun _ => rfl⟩
      | true =>
        rw [hSac] at hOut
        exact False.elim (mkRssSignAttemptOutcome_ne_err hOut)

private theorem rssThresholdSignMachine_attempt_mono
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {st₀ st_final : RssMlDsaSignerState}
    {trace : List (RssMlDsaAttemptInput × (RssSignPublicAbortView × Option ThresholdSignSig))}
    (hTr : (rssThresholdSignMachine chalHash sampleInBall).ValidTrace st₀ trace st_final) :
    st₀.nextAttempt ≤ st_final.nextAttempt ∧
    (∀ p ∈ trace, st₀.nextAttempt ≤ p.2.1.usedAttempt) ∧
    trace.Pairwise (fun p₁ p₂ => p₁.2.1.usedAttempt ≠ p₂.2.1.usedAttempt) := by
  induction hTr with
  | nil =>
    exact ⟨Nat.le_refl _, (fun _ hm => by cases hm), List.Pairwise.nil⟩
  | @accept sCur sNext sEnd inp out rest hStep _ ih =>
    dsimp only [rssThresholdSignMachine, PartyMachine.ofOutcome] at hStep
    cases hOut : rssThresholdSignStep chalHash sampleInBall sCur inp with
    | err _ _ => rw [hOut] at hStep; cases hStep
    | ok sOk outOk =>
      rw [hOut] at hStep
      injection hStep with hPair
      injection hPair with hStEq hOutEq
      subst hStEq hOutEq
      rcases outOk with ⟨pubView, mSig⟩
      obtain ⟨_, _, _, hNext, hUsed, _⟩ := rssThresholdSignStep_ok_meta hOut
      obtain ⟨hMonoTail, hGeTail, hPairTail⟩ := ih
      refine ⟨by omega, ?_, List.Pairwise.cons ?_ hPairTail⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hMem
        · dsimp only; omega
        · have h1 := hGeTail p hMem; omega
      · intro p₂ hp₂
        have h1 := hGeTail p₂ hp₂
        dsimp only; omega
  | @reject sCur sEnd inp rest _hNone _ ih =>
    obtain ⟨hErrGe, _⟩ := rssThresholdSignStep_err_attempt chalHash sampleInBall sCur inp
    obtain ⟨hMonoTail, hGeTail, hPairTail⟩ := ih
    refine ⟨by omega, fun p hp => ?_, hPairTail⟩
    have h1 := hGeTail p hp; omega

/-- **Flagship §2.4 Theorem — `(t, m)` Aggregate Rejection-Sampling Mask Bijection, RAM Attempt Counter &
    Parameterized Verification Completeness (`threshold_mldsa_rss_abort_leakage_and_completeness`, fixing `C0-1`)**:
    1. **Honest Abort Transcript & Unmasked-`z` Suppression (`rejectBit = true`)**: Whenever a valid
       attempt (`inp.epoch = st.epoch`, `inp.attempt = st.nextAttempt`, `rssProductsValid chalHash sampleInBall st inp = true`)
       violates `‖z‖_∞ < γ₁ - β`, `‖LowBits(w - c*s2)‖_∞ < γ₂ - β`, or `HighBits(w - c*s2) = HighBits(w)`,
       `rssThresholdSignStep` emits `(pubView, none)` (`pubView.rejectBit = true`, `pubView.openedW1 = HighBits(w)`,
       no separate unmasked `(z, h)` field) and burns `st'.nextAttempt = st.nextAttempt + 1`.
    2. **Explicit Leakage-Parameterized Abort Simulation (`rssAbortSimulator` + `rssMaskTripleEquiv`)**:
       Conditioned on the exact ideal abort leakage `(HighBits(w), rejectBit := true, inp.attempt)`,
       the `< q` RSS masks `(maskW, maskZ, maskLow)` map onto `(openedMaskedW, openedMaskedZ, openedMaskedLow)`
       via the constructive group bijection `rssMaskTripleEquiv w z u`, so `rssAbortSimulator` reproduces
       `pubView` identically with **zero** access to secret shares `(s1Subsets, s2Subsets, ySubsets)`!
    3. **Multi-Turn Attempt-Burn Uniqueness (`PartyMachine.ValidTrace`)**: Across ANY multi-turn trace of
       interleaved rejected and accepted attempts, `nextAttempt` is monotonically non-decreasing and every
       emitted transcript uses a strictly distinct `usedAttempt` index.
    4. **Parameterized algebraic `mldsaVerify` completeness**: Every accepted signature `some sig` satisfies
       `pubView.rejectBit = false` and `mldsaVerify = true` under the RSS aggregate public key! -/
theorem threshold_mldsa_rss_abort_leakage_and_completeness
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    let M := rssThresholdSignMachine chalHash sampleInBall
    (∀ (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput),
      inp.epoch = st.epoch →
      inp.attempt = st.nextAttempt →
      rssProductsValid chalHash sampleInBall st inp = true →
      let s1 := rssSumVec4List st.s1Subsets
      let s2 := rssSumVec4List st.s2Subsets
      let y := rssSumVec4List inp.ySubsets
      let w := matVecMul4 st.A y
      let w1 := highBitsVec4 w
      let c := sampleInBall (chalHash inp.mu w1)
      let z := addVec4 y (mulPolyVec4 c s1)
      let u := subVec4 w (mulPolyVec4 c s2)
      (¬ (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) ∨
       ¬ (lowBitsNormVec4 u < mldsa44Gamma2 - mldsa44Beta) ∨
       highBitsVec4 u ≠ w1) →
      ∃ (st' : RssMlDsaSignerState) (pubView : RssSignPublicAbortView),
        M.step st inp = some (st', (pubView, none)) ∧
        st'.nextAttempt = st.nextAttempt + 1 ∧
        pubView.rejectBit = true ∧
        pubView.openedW1 = w1 ∧
        rssAbortSimulator w1 inp.attempt
          ((rssMaskTripleEquiv w z u).toFun (inp.maskW, inp.maskZ, inp.maskLow)) = pubView) ∧
    (∀ (st₀ st_final : RssMlDsaSignerState)
       (trace : List (RssMlDsaAttemptInput × (RssSignPublicAbortView × Option ThresholdSignSig))),
      M.ValidTrace st₀ trace st_final →
      st₀.nextAttempt ≤ st_final.nextAttempt ∧
      trace.Pairwise (fun p₁ p₂ => p₁.2.1.usedAttempt ≠ p₂.2.1.usedAttempt)) ∧
    (∀ (st st' : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
       (pubView : RssSignPublicAbortView) (sig : ThresholdSignSig),
      M.step st inp = some (st', (pubView, some sig)) →
      pubView.rejectBit = false ∧
      mldsaVerify chalHash sampleInBall st.A
        (power2RoundHighVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))
        inp.mu sig.cTilde sig.z sig.h = true) := by
  intro M
  refine ⟨?_, ?_, ?_⟩
  · intro st inp hEp hAtt hSac s1 s2 y w w1 c z u hRejCond
    have hAccFalse :
        (decide (infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))) < mldsa44Gamma2) &&
         decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
         decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
         decide (hintWeightVec4 (makeHintVec4
           (negVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))))
           (addVec4 u (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))))) ≤ mldsa44Omega)) = false := by
      cases hBool :
          (decide (infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))) < mldsa44Gamma2) &&
           decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
           decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
           decide (hintWeightVec4 (makeHintVec4
             (negVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))))
             (addVec4 u (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))))) ≤ mldsa44Omega)) with
      | false => rfl
      | true =>
        exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hBool
        rcases hBool with ⟨⟨⟨_, hzLt⟩, hDiffLt⟩, _⟩
        have hB : mldsa44Gamma2 - mldsa44Beta ≤ 95232 := by decide
        obtain ⟨hLowLt, hHighEq⟩ := (centeredDiffNormVec4_lt_iff u w hB).mp hDiffLt
        rcases hRejCond with hBadZ | hBadLow | hBadHigh
        · exact hBadZ hzLt
        · exact hBadLow hLowLt
        · exact hBadHigh hHighEq
    let stBurned : RssMlDsaSignerState := { st with nextAttempt := st.nextAttempt + 1 }
    let pubView : RssSignPublicAbortView :=
      { openedMaskedW := addVec4 w inp.maskW
        openedW1 := w1
        openedMaskedZ := addVec4 z inp.maskZ
        openedMaskedLow := addVec4 u inp.maskLow
        rejectBit := true
        usedAttempt := inp.attempt }
    refine ⟨stBurned, pubView, ?_, rfl, rfl, rfl, rfl⟩
    dsimp only [M, rssThresholdSignMachine, PartyMachine.ofOutcome]
    have hStepFalse : rssThresholdSignStep chalHash sampleInBall st inp = .ok stBurned (pubView, none) := by
      unfold rssThresholdSignStep rssSignCore
      rw [decide_eq_true ⟨hEp, hAtt⟩, hSac]
      rw [(rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp hSac]
      dsimp only [rssComputeProducts]
      exact mkRssSignAttemptOutcome_false stBurned inp.attempt (chalHash inp.mu w1)
        w z u inp.maskW inp.maskZ inp.maskLow w1 _ hAccFalse
    rw [hStepFalse]
  · intro st₀ st_final trace hTr
    obtain ⟨hMono, _, hPair⟩ := rssThresholdSignMachine_attempt_mono hTr
    exact ⟨hMono, hPair⟩
  · intro st st' inp pubView sig hStep
    dsimp only [M, rssThresholdSignMachine, PartyMachine.ofOutcome] at hStep
    cases hOut : rssThresholdSignStep chalHash sampleInBall st inp with
    | err _ _ => rw [hOut] at hStep; cases hStep
    | ok stOk outOk =>
      rw [hOut] at hStep
      injection hStep with hPair
      injection hPair with hStEq hOutEq
      subst hStEq hOutEq
      have hSpec := (rssThresholdSignStep_ok_meta hOut).2.2.2.2.2 sig rfl
      exact ⟨hSpec.1, hSpec.2.2⟩

private def natTreeList204 : {d : Nat} → NatTree d → List Nat
  | 0, .leaf n => [n]
  | _ + 1, .branch l r => natTreeList204 l ++ natTreeList204 r

private def packSix204 : List Nat → List UInt8
  | a :: b :: c :: d :: rest =>
    UInt8.ofNat (a + 64 * b) :: UInt8.ofNat (b / 4 + 16 * c) ::
      UInt8.ofNat (c / 16 + 4 * d) :: packSix204 rest
  | _ => []

def mldsa44ChallengeHash (mu : List UInt8) (w1 : Fin 4 → NatTree 8) : List UInt8 :=
  shake256Xof 32 (mu ++ ((List.finRange 4).flatMap (fun i => packSix204 (natTreeList204 (w1 i)))))

/-- Non-vacuous inhabitedness witness for `rssThresholdSignMachine` exercising BOTH:
    (i) an accepted RSS attempt emitting `some sig` with `mldsaVerify = true` and `rejectBit = false`, AND
    (ii) a boundary-rejected RSS attempt emitting `(pubViewRej, none)` with `rejectBit = true`! -/
theorem threshold_mldsa_rss_inhabited :
    ∃ (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
      (sampleInBall : List UInt8 → Poly256)
      (st stAcc stRej : RssMlDsaSignerState)
      (inpAcc inpRej : RssMlDsaAttemptInput)
      (pubAcc pubRej : RssSignPublicAbortView)
      (sig : ThresholdSignSig),
      (rssThresholdSignMachine chalHash sampleInBall).step st inpAcc = some (stAcc, (pubAcc, some sig)) ∧
      pubAcc.rejectBit = false ∧
      mldsaVerify chalHash sampleInBall st.A
        (power2RoundHighVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))
        inpAcc.mu sig.cTilde sig.z sig.h = true ∧
      (rssThresholdSignMachine chalHash sampleInBall).step st inpRej = some (stRej, (pubRej, none)) ∧
      pubRej.rejectBit = true ∧
      st.epoch = 0 ∧ st.nextAttempt = 0 ∧
      inpAcc.products = rssComputeProducts chalHash sampleInBall st inpAcc.mu inpAcc.ySubsets ∧
      rssSumVec4List st.s1Subsets ≠ rssZeroVec4 := by
  let chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8 := mldsa44ChallengeHash
  let sampleInBall : List UInt8 → Poly256 := fun _ => PolyTree.constUnit 8
  let p1 : Poly256 := polyTreeConstLeaf 8 Fq204.one
  let v1 : PolyVec4 := fun _ => p1
  let yBad : PolyVec4 := fun _ => polyTreeConstLeaf 8 ⟨131072, by decide⟩
  let st : RssMlDsaSignerState :=
    { epoch := 0, nextAttempt := 0, A := shiftMat4, s1Subsets := [v1], s2Subsets := [v1] }
  let inpAcc : RssMlDsaAttemptInput :=
    { epoch := 0, sessionId := [0x01], attempt := 0, mu := [0x42],
      ySubsets := [v1], maskW := v1, maskZ := v1, maskLow := v1,
      products := rssComputeProducts chalHash sampleInBall st [0x42] [v1] }
  let inpRej : RssMlDsaAttemptInput :=
    { epoch := 0, sessionId := [0x01], attempt := 0, mu := [0x42],
      ySubsets := [yBad], maskW := v1, maskZ := v1, maskLow := v1,
      products := rssComputeProducts chalHash sampleInBall st [0x42] [yBad] }
  have hSum1 : rssSumVec4List [v1] = v1 := by
    dsimp only [rssSumVec4List]; exact addVec4_rssZero_right v1
  have hSumBad : rssSumVec4List [yBad] = yBad := by
    dsimp only [rssSumVec4List]; exact addVec4_rssZero_right yBad
  have hMv : matVecMul4 shiftMat4 v1 = v1 := matVecMul4_shiftMat4_const p1
  have hMul1 : ∀ w : PolyVec4, mulPolyVec4 (PolyTree.constUnit 8) w = w := fun w => by
    funext i; exact negacyclicMul_one_left (w i)
  have hAddV1 : addVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 (Fq204.add Fq204.one Fq204.one)) := by
    funext i; exact polyTreeConstLeaf_add Fq204.one Fq204.one 8
  have hSubSelf : subVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 Fq204.zero) := by
    funext i; dsimp only [subVec4, v1]
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm, polyTree_add_left_neg, polyTreeConstLeaf_zero_eq]
  have hCt0 : infNormVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))) <
      mldsa44Gamma2 := by
    rw [hMv, hMul1, hAddV1]
    unfold infNormVec4 power2RoundLowVec4
    dsimp only
    simp only [polyTreeConstLeaf_power2RoundLow, polyTreeConstLeaf_infNorm, Nat.max_self]
    decide
  have hZ : infNormVec4 (addVec4 v1 (mulPolyVec4 (PolyTree.constUnit 8) v1)) < mldsa44Gamma1 - mldsa44Beta := by
    rw [hMul1, hAddV1]
    unfold infNormVec4
    dsimp only
    simp only [polyTreeConstLeaf_infNorm, Nat.max_self]
    decide
  have hDiff : centeredDiffNormVec4 (subVec4 (matVecMul4 shiftMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
      (highBitsVec4 (matVecMul4 shiftMat4 v1)) < mldsa44Gamma2 - mldsa44Beta := by
    rw [hMv, hMul1, hSubSelf]
    unfold centeredDiffNormVec4 highBitsVec4
    dsimp only [v1, p1]
    simp only [polyTreeConstLeaf_centeredDiffNorm, Nat.max_self]
    decide
  have hW : hintWeightVec4 (makeHintVec4
      (negVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))))
      (addVec4 (subVec4 (matVecMul4 shiftMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
               (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))))) ≤
      mldsa44Omega := by
    rw [hMv, hMul1, hMul1, hSubSelf, hAddV1]
    unfold hintWeightVec4 makeHintVec4 negVec4 addVec4 power2RoundLowVec4
    dsimp only
    simp only [polyTreeConstLeaf_power2RoundLow, polyTreeConstLeaf_neg,
      polyTreeConstLeaf_add, polyTreeConstLeaf_hintWeight]
    decide
  have hAcc :
      (decide (infNormVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))) < mldsa44Gamma2) &&
       decide (infNormVec4 (addVec4 v1 (mulPolyVec4 (PolyTree.constUnit 8) v1)) < mldsa44Gamma1 - mldsa44Beta) &&
       decide (centeredDiffNormVec4 (subVec4 (matVecMul4 shiftMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
         (highBitsVec4 (matVecMul4 shiftMat4 v1)) < mldsa44Gamma2 - mldsa44Beta) &&
       decide (hintWeightVec4 (makeHintVec4
         (negVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))))
         (addVec4 (subVec4 (matVecMul4 shiftMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
                  (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))))) ≤ mldsa44Omega)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hCt0, hZ⟩, hDiff⟩, hW⟩
  have hZBad : ¬ (infNormVec4 (addVec4 (rssSumVec4List inpRej.ySubsets)
      (mulPolyVec4 (sampleInBall (chalHash inpRej.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpRej.ySubsets)))))
        (rssSumVec4List st.s1Subsets))) < mldsa44Gamma1 - mldsa44Beta) := by
    dsimp only [st, inpRej, sampleInBall, chalHash]
    rw [hSumBad, hSum1, hMul1]
    have hAddBad : addVec4 yBad v1 = (fun _ => polyTreeConstLeaf 8 (Fq204.add ⟨131072, by decide⟩ Fq204.one)) := by
      funext i; exact polyTreeConstLeaf_add ⟨131072, by decide⟩ Fq204.one 8
    rw [hAddBad]
    unfold infNormVec4
    dsimp only
    simp only [polyTreeConstLeaf_infNorm, Nat.max_self]
    decide
  obtain ⟨stRej, pubRej, hStepRej, _, hRejBit, _, _⟩ :=
    (threshold_mldsa_rss_abort_leakage_and_completeness chalHash sampleInBall).1 st inpRej rfl rfl
      ((rssProductsValid_eq_true_iff chalHash sampleInBall st inpRej).mpr rfl) (Or.inl hZBad)
  have hAccFull :
      (decide (infNormVec4 (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
        (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))) < mldsa44Gamma2) &&
       decide (infNormVec4 (addVec4 (rssSumVec4List inpAcc.ySubsets)
         (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
           (rssSumVec4List st.s1Subsets))) < mldsa44Gamma1 - mldsa44Beta) &&
       decide (centeredDiffNormVec4
         (subVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets))
           (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
             (rssSumVec4List st.s2Subsets)))
         (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets))) < mldsa44Gamma2 - mldsa44Beta) &&
       decide (hintWeightVec4 (makeHintVec4
         (negVec4 (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
           (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))))
         (addVec4 (subVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets))
           (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
             (rssSumVec4List st.s2Subsets)))
           (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
             (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))))) ≤ mldsa44Omega)) = true := by
    dsimp only [st, inpAcc, sampleInBall, chalHash]
    rw [hSum1]
    exact hAcc
  let s1Acc := rssSumVec4List st.s1Subsets
  let s2Acc := rssSumVec4List st.s2Subsets
  let yAcc := rssSumVec4List inpAcc.ySubsets
  let t0Acc := power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1Acc) s2Acc)
  let wAcc := matVecMul4 st.A yAcc
  let w1Acc := highBitsVec4 wAcc
  let cTildeAcc := chalHash inpAcc.mu w1Acc
  let cAcc := sampleInBall cTildeAcc
  let ct0Acc := mulPolyVec4 cAcc t0Acc
  let zAcc := addVec4 yAcc (mulPolyVec4 cAcc s1Acc)
  let uAcc := subVec4 wAcc (mulPolyVec4 cAcc s2Acc)
  let hintAcc := makeHintVec4 (negVec4 ct0Acc) (addVec4 uAcc ct0Acc)
  have hStepAcc :
      (rssThresholdSignMachine chalHash sampleInBall).step st inpAcc =
        some ({ st with nextAttempt := st.nextAttempt + 1 },
          ({ openedMaskedW := addVec4 wAcc inpAcc.maskW,
             openedW1 := w1Acc,
             openedMaskedZ := addVec4 zAcc inpAcc.maskZ,
             openedMaskedLow := addVec4 uAcc inpAcc.maskLow,
             rejectBit := false,
             usedAttempt := inpAcc.attempt },
           some { cTilde := cTildeAcc,
                  z := zAcc,
                  h := hintAcc,
                  usedAttempt := inpAcc.attempt })) :=
    rssThresholdSignMachine_step_accept chalHash sampleInBall st inpAcc rfl rfl rfl hAccFull
  obtain ⟨hRejFalse, hVer⟩ :=
    (threshold_mldsa_rss_abort_leakage_and_completeness chalHash sampleInBall).2.2 _ _ _ _ _ hStepAcc
  have hNz : rssSumVec4List st.s1Subsets ≠ rssZeroVec4 := by
    dsimp only [st]
    rw [hSum1]
    intro h
    have he : polyTreeConstLeaf 8 Fq204.one = PolyTree.zero 8 := congrFun h (0 : Fin 4)
    have hv := congrArg PolyTree.infNorm he
    rw [polyTreeConstLeaf_infNorm] at hv
    change 1 = 0 at hv
    omega
  exact ⟨chalHash, sampleInBall, st, _, stRej, inpAcc, inpRej, _, pubRej, _,
         hStepAcc, hRejFalse, hVer, hStepRej, hRejBit, rfl, rfl, rfl, hNz⟩

/-! ## §3. Dealerless 2-of-5 Replicated Poseidon2 Threshold OPRF (`voprf.rs` / `toprf_engine.rs`, `P0-08`–`P0-09`) -/

/-! ### §3.1 Combinatorial $\binom{5}{3} = 10$ Subset Coverage & Cross-Term Holder Invariant -/

/-- Exact ascending enumeration of all $\binom{5}{3} = 10$ 3-server subsets of `Fin 5`. -/
def subsets3Of5 : List (List (Fin 5)) :=
  [ [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4],
    [0, 3, 4], [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4] ]

/-- **Combinatorial $\binom{5}{3} = 10$ Pairwise Intersection Theorem (`subsets3Of5_intersect_nonempty`)**:
    Every pair `(A, B)` of 3-server subsets in `(t = 2, n = 5)` replicated secret sharing shares
    at least $3 + 3 - 5 = 1$ common server (`∃ s : Fin 5, s ∈ A ∧ s ∈ B`). -/
theorem subsets3Of5_intersect_nonempty :
    subsets3Of5.length = 10 ∧
    subsets3Of5.Nodup ∧
    (∀ A ∈ subsets3Of5, A.length = 3 ∧ A.Nodup) ∧
    (∀ A ∈ subsets3Of5, ∀ B ∈ subsets3Of5, ∃ s : Fin 5, s ∈ A ∧ s ∈ B) := by
  decide

/-- **`#tooth` (`tooth_subsets2Of5_disjoint`)**:
    Shrinking subset size from $3$ to $2$ on $n = 5$ servers ($t = 3$, violating $5 \ge 2 \cdot 3 - 1$? No:
    $5 = 2 \cdot 3 - 1$ has subset size $5 - 3 + 1 = 3$, whereas $t = 4$ has subset size $2 < 5/2$)
    admits disjoint subsets `[0, 1]` and `[2, 3]` with **zero** common server to evaluate cross-products! -/
theorem tooth_subsets2Of5_disjoint :
    let A : List (Fin 5) := [0, 1]
    let B : List (Fin 5) := [2, 3]
    A.length = 2 ∧ B.length = 2 ∧ A.Nodup ∧ B.Nodup ∧
    (∀ s : Fin 5, ¬ (s ∈ A ∧ s ∈ B)) := by
  decide

def fin5List : List (Fin 5) := [0, 1, 2, 3, 4]

/-- The 4 servers holding additive component `c` (`party != c`, `voprf.rs:410, 514, 598`). -/
def fin5Others (c : Fin 5) : List (Fin 5) :=
  fin5List.filter (fun p => decide (p ≠ c))

/-- The 3 ascending holders of ordered cross-term `(i, j)` (`i ≠ j`), matching `toprf_engine.rs:103-113`. -/
def toprfHolders (i j : Fin 5) : List (Fin 5) :=
  fin5List.filter (fun p => decide (p ≠ i) && decide (p ≠ j))

/-- Every component `c` is held by 4 distinct servers, and every off-diagonal cross-term `(i, j)` (`i ≠ j`)
    is held by a 3-server subset `toprfHolders i j ∈ subsets3Of5`! -/
theorem toprfHolders_spec :
    (∀ c : Fin 5,
      (fin5Others c).length = 4 ∧
      (fin5Others c).Nodup ∧
      (∀ p : Fin 5, p ∈ fin5Others c ↔ p ≠ c)) ∧
    (∀ i j : Fin 5, i ≠ j →
      (toprfHolders i j).length = 3 ∧
      (toprfHolders i j).Nodup ∧
      (toprfHolders i j ∈ subsets3Of5) ∧
      (∀ p : Fin 5, p ∈ toprfHolders i j ↔ (p ≠ i ∧ p ≠ j))) := by
  decide

private theorem fin5Others_0 : fin5Others 0 = [1, 2, 3, 4] := by decide
private theorem fin5Others_1 : fin5Others 1 = [0, 2, 3, 4] := by decide
private theorem fin5Others_2 : fin5Others 2 = [0, 1, 3, 4] := by decide
private theorem fin5Others_3 : fin5Others 3 = [0, 1, 2, 4] := by decide
private theorem fin5Others_4 : fin5Others 4 = [0, 1, 2, 3] := by decide

/-! ### §3.2 Exact 5-Component Replicated Arithmetic Engine & 30-Round `Poseidon2` Simulation -/

/-- 5-component additive wire `Wire = [u64; 5]` over `Goldilocks` (`toprf_engine.rs:38`). -/
abbrev ToprfWire := Fin 5 → Goldilocks

/-- Sum of all 5 additive components of a `ToprfWire`. -/
def sumWire5 (w : ToprfWire) : Goldilocks :=
  Goldilocks.add
    (Goldilocks.add
      (Goldilocks.add (Goldilocks.add (w 0) (w 1)) (w 2))
      (w 3))
    (w 4)

def sumGoldList : List Goldilocks → Goldilocks
  | [] => Goldilocks.zero
  | a :: as => Goldilocks.add a (sumGoldList as)

/-- Exact 5-component replicated multiplication `z = x * y` (`toprf_engine.rs:244-300`):
    - Component `c` accumulates diagonal `x_c * y_c`,
    - Outgoing masks `+ ∑_{j ≠ c} mask(c, j)` (`z[i] += r`),
    - Incoming masked cross-terms `+ ∑_{i ≠ c} (x_i * y_c - mask(i, c))` (`z[j] += x_i * y_j - r`). -/
def toprfMulWire (x y : ToprfWire) (mask : Fin 5 → Fin 5 → Goldilocks) : ToprfWire :=
  fun c =>
    let diag := Goldilocks.mul (x c) (y c)
    let outMasks := sumGoldList ((fin5Others c).map (fun j => mask c j))
    let inTerms := sumGoldList ((fin5Others c).map (fun i =>
      Goldilocks.sub (Goldilocks.mul (x i) (y c)) (mask i c)))
    Goldilocks.add (Goldilocks.add diag outMasks) inTerms

/-- **5-Component Replicated Multiplication Soundness (`toprfMulWire_sum`)**:
    For ANY 20 off-diagonal masks `mask i j`, all `+ mask(i, j)` and `- mask(i, j)` terms cancel
    exact-algebraically across components `i` and `j`, leaving all 25 terms `∑_{i,j} x_i * y_j = (∑ x_i)*(∑ y_j)`. -/
theorem toprfMulWire_sum (x y : ToprfWire) (mask : Fin 5 → Fin 5 → Goldilocks) :
    sumWire5 (toprfMulWire x y mask) = Goldilocks.mul (sumWire5 x) (sumWire5 y) := by
  unfold sumWire5 toprfMulWire
  rw [fin5Others_0, fin5Others_1, fin5Others_2, fin5Others_3, fin5Others_4]
  dsimp only [List.map, sumGoldList]
  have hz : Goldilocks.zero = goldOfInt 0 := rfl
  rw [hz,
      ← goldOfInt_nat (x 0), ← goldOfInt_nat (x 1), ← goldOfInt_nat (x 2),
      ← goldOfInt_nat (x 3), ← goldOfInt_nat (x 4),
      ← goldOfInt_nat (y 0), ← goldOfInt_nat (y 1), ← goldOfInt_nat (y 2),
      ← goldOfInt_nat (y 3), ← goldOfInt_nat (y 4),
      ← goldOfInt_nat (mask 0 1), ← goldOfInt_nat (mask 0 2), ← goldOfInt_nat (mask 0 3), ← goldOfInt_nat (mask 0 4),
      ← goldOfInt_nat (mask 1 0), ← goldOfInt_nat (mask 1 2), ← goldOfInt_nat (mask 1 3), ← goldOfInt_nat (mask 1 4),
      ← goldOfInt_nat (mask 2 0), ← goldOfInt_nat (mask 2 1), ← goldOfInt_nat (mask 2 3), ← goldOfInt_nat (mask 2 4),
      ← goldOfInt_nat (mask 3 0), ← goldOfInt_nat (mask 3 1), ← goldOfInt_nat (mask 3 2), ← goldOfInt_nat (mask 3 4),
      ← goldOfInt_nat (mask 4 0), ← goldOfInt_nat (mask 4 1), ← goldOfInt_nat (mask 4 2), ← goldOfInt_nat (mask 4 3)]
  simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
  congr 1
  simp only [Int.add_mul, Int.mul_add]
  omega

/-- Replicated depth-3 S-box `x ↦ x^7` (`x^2 -> (x^3, x^4) -> x^7`, `toprf_engine.rs:305-313`). -/
def toprfSboxWire (w : ToprfWire)
    (m1 m2 m3 m4 : Fin 5 → Fin 5 → Goldilocks) : ToprfWire :=
  let x2 := toprfMulWire w w m1
  let x3 := toprfMulWire x2 w m2
  let x4 := toprfMulWire x2 x2 m3
  toprfMulWire x3 x4 m4

theorem toprfSboxWire_sum (w : ToprfWire) (m1 m2 m3 m4 : Fin 5 → Fin 5 → Goldilocks) :
    sumWire5 (toprfSboxWire w m1 m2 m3 m4) = sbox7 (sumWire5 w) := by
  unfold toprfSboxWire sbox7
  dsimp only
  simp only [toprfMulWire_sum]

/-- 5-component replicated Width-12 `Poseidon2` state (`[Wire; 12]`, `toprf_engine.rs:83`). -/
abbrev ToprfState12 := Fin 5 → Poseidon2State12

/-- Reconstruct plaintext `Poseidon2State12` by summing the 5 replicated component columns. -/
def sumToprfState12 (st : ToprfState12) : Poseidon2State12 :=
  state12Add (state12Add (state12Add (state12Add (st 0) (st 1)) (st 2)) (st 3)) (st 4)

private theorem sumToprfState12_lanes (st : ToprfState12) :
    sumToprfState12 st =
      ⟨⟨sumWire5 (fun c => (st c).b0.x0), sumWire5 (fun c => (st c).b0.x1),
        sumWire5 (fun c => (st c).b0.x2), sumWire5 (fun c => (st c).b0.x3)⟩,
       ⟨sumWire5 (fun c => (st c).b1.x0), sumWire5 (fun c => (st c).b1.x1),
        sumWire5 (fun c => (st c).b1.x2), sumWire5 (fun c => (st c).b1.x3)⟩,
       ⟨sumWire5 (fun c => (st c).b2.x0), sumWire5 (fun c => (st c).b2.x1),
        sumWire5 (fun c => (st c).b2.x2), sumWire5 (fun c => (st c).b2.x3)⟩⟩ := by
  unfold sumToprfState12 sumWire5
  simp only [state12Add_eq, lane4Add_eq]

/-- Public constant addition into component `0` (`if party != 0 { st[0] = gl_add(st[0], v) }`, `toprf_engine.rs:96-100`). -/
def toprfAddPublicState12 (rc : Poseidon2State12) (st : ToprfState12) : ToprfState12 :=
  fun c => if c = 0 then state12Add (st 0) rc else st c

private theorem sumWire5_add_comp0 (w : ToprfWire) (v : Goldilocks) :
    sumWire5 (fun c => if c = 0 then Goldilocks.add (w 0) v else w c) =
      Goldilocks.add (sumWire5 w) v := by
  unfold sumWire5
  have h1 : (1 : Fin 5) ≠ 0 := by decide
  have h2 : (2 : Fin 5) ≠ 0 := by decide
  have h3 : (3 : Fin 5) ≠ 0 := by decide
  have h4 : (4 : Fin 5) ≠ 0 := by decide
  simp only [↓reduceIte, h1, h2, h3, h4]
  rw [← goldOfInt_nat (w 0), ← goldOfInt_nat (w 1), ← goldOfInt_nat (w 2),
      ← goldOfInt_nat (w 3), ← goldOfInt_nat (w 4), ← goldOfInt_nat v]
  simp only [goldOfInt_add]
  congr 1
  omega

theorem sumToprfState12_addPublic (rc : Poseidon2State12) (st : ToprfState12) :
    sumToprfState12 (toprfAddPublicState12 rc st) = state12Add (sumToprfState12 st) rc := by
  rw [sumToprfState12_lanes, sumToprfState12_lanes, state12Add_eq]
  dsimp only [toprfAddPublicState12]
  have hProj : ∀ (f : Poseidon2State12 → Goldilocks)
      (hf : ∀ a b, f (state12Add a b) = Goldilocks.add (f a) (f b)),
      (fun c : Fin 5 => f (if c = 0 then state12Add (st 0) rc else st c)) =
        (fun c : Fin 5 => if c = 0 then Goldilocks.add (f (st 0)) (f rc) else f (st c)) := by
    intro f hf
    funext c
    by_cases hc : c = 0
    · subst hc; simp only [↓reduceIte, hf]
    · simp only [hc, ↓reduceIte]
  rw [hProj (fun q => q.b0.x0) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b0.x1) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b0.x2) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b0.x3) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b1.x0) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b1.x1) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b1.x2) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b1.x3) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b2.x0) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b2.x1) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b2.x2) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b2.x3) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      sumWire5_add_comp0 (fun c => (st c).b0.x0),
      sumWire5_add_comp0 (fun c => (st c).b0.x1),
      sumWire5_add_comp0 (fun c => (st c).b0.x2),
      sumWire5_add_comp0 (fun c => (st c).b0.x3),
      sumWire5_add_comp0 (fun c => (st c).b1.x0),
      sumWire5_add_comp0 (fun c => (st c).b1.x1),
      sumWire5_add_comp0 (fun c => (st c).b1.x2),
      sumWire5_add_comp0 (fun c => (st c).b1.x3),
      sumWire5_add_comp0 (fun c => (st c).b2.x0),
      sumWire5_add_comp0 (fun c => (st c).b2.x1),
      sumWire5_add_comp0 (fun c => (st c).b2.x2),
      sumWire5_add_comp0 (fun c => (st c).b2.x3)]
  simp only [lane4Add_eq]

private theorem sumToprfState12_applyME (f : Fin 5 → Poseidon2State12) :
    sumToprfState12 (fun c => applyME (f c)) = applyME (sumToprfState12 f) := by
  unfold sumToprfState12
  rw [← applyME_add, ← applyME_add, ← applyME_add, ← applyME_add]

private theorem sumToprfState12_applyMI (f : Fin 5 → Poseidon2State12) :
    sumToprfState12 (fun c => applyMI (f c)) = applyMI (sumToprfState12 f) := by
  unfold sumToprfState12
  rw [← applyMI_add, ← applyMI_add, ← applyMI_add, ← applyMI_add]

/-- Per-S-box 4-gate mask bundle (`m1, m2, m3, m4 : Fin 5 → Fin 5 → Goldilocks`). -/
structure SboxMask4 where
  m1 : Fin 5 → Fin 5 → Goldilocks
  m2 : Fin 5 → Fin 5 → Goldilocks
  m3 : Fin 5 → Fin 5 → Goldilocks
  m4 : Fin 5 → Fin 5 → Goldilocks

/-- Replicated external full-width S-box + `applyME` round (`toprf_engine.rs:318-337`). -/
def toprfExtRound (masks : Fin 12 → SboxMask4) (rc : Poseidon2State12) (st : ToprfState12) : ToprfState12 :=
  let s := toprfAddPublicState12 rc st
  let sb (idx : Fin 12) (f : Poseidon2State12 → Goldilocks) : ToprfWire :=
    let m := masks idx
    toprfSboxWire (fun c => f (s c)) m.m1 m.m2 m.m3 m.m4
  let y0 := sb ⟨0, by decide⟩ (fun q => q.b0.x0)
  let y1 := sb ⟨1, by decide⟩ (fun q => q.b0.x1)
  let y2 := sb ⟨2, by decide⟩ (fun q => q.b0.x2)
  let y3 := sb ⟨3, by decide⟩ (fun q => q.b0.x3)
  let y4 := sb ⟨4, by decide⟩ (fun q => q.b1.x0)
  let y5 := sb ⟨5, by decide⟩ (fun q => q.b1.x1)
  let y6 := sb ⟨6, by decide⟩ (fun q => q.b1.x2)
  let y7 := sb ⟨7, by decide⟩ (fun q => q.b1.x3)
  let y8 := sb ⟨8, by decide⟩ (fun q => q.b2.x0)
  let y9 := sb ⟨9, by decide⟩ (fun q => q.b2.x1)
  let y10 := sb ⟨10, by decide⟩ (fun q => q.b2.x2)
  let y11 := sb ⟨11, by decide⟩ (fun q => q.b2.x3)
  fun c => applyME ⟨⟨y0 c, y1 c, y2 c, y3 c⟩, ⟨y4 c, y5 c, y6 c, y7 c⟩, ⟨y8 c, y9 c, y10 c, y11 c⟩⟩

/-- Replicated internal lane-0 S-box + `applyMI` round (`toprf_engine.rs:318-337`). -/
def toprfIntRound (m : SboxMask4) (rc : Goldilocks) (st : ToprfState12) : ToprfState12 :=
  let w0 : ToprfWire := fun c => if c = 0 then Goldilocks.add (st 0).b0.x0 rc else (st c).b0.x0
  let y0 := toprfSboxWire w0 m.m1 m.m2 m.m3 m.m4
  fun c => applyMI ⟨⟨y0 c, (st c).b0.x1, (st c).b0.x2, (st c).b0.x3⟩, (st c).b1, (st c).b2⟩

theorem sumToprfState12_extRound (masks : Fin 12 → SboxMask4) (rc : Poseidon2State12) (st : ToprfState12) :
    sumToprfState12 (toprfExtRound masks rc st) = externalRound rc (sumToprfState12 st) := by
  unfold toprfExtRound
  dsimp only
  rw [sumToprfState12_applyME, externalRound_eq, ← sumToprfState12_addPublic rc st]
  congr 1
  rw [sumToprfState12_lanes, sboxState12_eq, sumToprfState12_lanes]
  dsimp only
  simp only [toprfSboxWire_sum]

theorem sumToprfState12_intRound (m : SboxMask4) (rc : Goldilocks) (st : ToprfState12) :
    sumToprfState12 (toprfIntRound m rc st) = internalRound rc (sumToprfState12 st) := by
  unfold toprfIntRound
  dsimp only
  rw [sumToprfState12_applyMI, internalRound_eq]
  congr 1
  rw [sumToprfState12_lanes, sumToprfState12_lanes]
  dsimp only
  rw [toprfSboxWire_sum, sumWire5_add_comp0 (fun c => (st c).b0.x0)]

/-- Mask schedule for all 30 rounds (`4` initial external + `22` internal + `4` terminal external) of `poseidon2Perm12`. -/
structure ToprfPerm12Masks where
  initExt : Nat → Fin 12 → SboxMask4
  internal : Nat → SboxMask4
  termExt : Nat → Fin 12 → SboxMask4

def runToprfRoundsIdx {α : Type} (step : Nat → α → ToprfState12 → ToprfState12) :
    Nat → List α → ToprfState12 → ToprfState12
  | _, [], st => st
  | idx, c :: cs, st => runToprfRoundsIdx step (idx + 1) cs (step idx c st)

private theorem sumToprfState12_runExtRounds (maskFn : Nat → Fin 12 → SboxMask4) :
    ∀ (idx : Nat) (rcs : List Poseidon2State12) (st : ToprfState12),
      sumToprfState12 (runToprfRoundsIdx (fun r rc s => toprfExtRound (maskFn r) rc s) idx rcs st) =
        runRounds externalRound rcs (sumToprfState12 st)
  | _, [], st => by rw [runRounds_nil]; rfl
  | idx, rc :: rcs, st => by
    dsimp only [runToprfRoundsIdx]
    rw [runRounds_cons, ← sumToprfState12_extRound (maskFn idx) rc st]
    exact sumToprfState12_runExtRounds maskFn (idx + 1) rcs _

private theorem sumToprfState12_runIntRounds (maskFn : Nat → SboxMask4) :
    ∀ (idx : Nat) (rcs : List Goldilocks) (st : ToprfState12),
      sumToprfState12 (runToprfRoundsIdx (fun r rc s => toprfIntRound (maskFn r) rc s) idx rcs st) =
        runRounds internalRound rcs (sumToprfState12 st)
  | _, [], st => by rw [runRounds_nil]; rfl
  | idx, rc :: rcs, st => by
    dsimp only [runToprfRoundsIdx]
    rw [runRounds_cons, ← sumToprfState12_intRound (maskFn idx) rc st]
    exact sumToprfState12_runIntRounds maskFn (idx + 1) rcs _

/-- Full 30-round replicated Width-12 `Poseidon2` evaluation (`Engine::permute`, `toprf_engine.rs:314-340`). -/
def toprfEvalPerm12 (masks : ToprfPerm12Masks) (init : ToprfState12) : ToprfState12 :=
  let s0 : ToprfState12 := fun c => applyME (init c)
  let s1 := runToprfRoundsIdx (fun r rc s => toprfExtRound (masks.initExt r) rc s) 0 poseidon2InitialExtConsts s0
  let s2 := runToprfRoundsIdx (fun r rc s => toprfIntRound (masks.internal r) rc s) 0 poseidon2InternalConsts s1
  runToprfRoundsIdx (fun r rc s => toprfExtRound (masks.termExt r) rc s) 0 poseidon2TerminalExtConsts s2

/-- **End-to-End 30-Round Replicated `Poseidon2` Simulation Theorem (`toprfEvalPerm12_sum`)**:
    Across all 4 initial external rounds, 22 internal rounds, and 4 terminal external rounds,
    summing the 5 replicated server components equals `poseidon2Perm12 (sumToprfState12 init)` identically! -/
theorem toprfEvalPerm12_sum (masks : ToprfPerm12Masks) (init : ToprfState12) :
    sumToprfState12 (toprfEvalPerm12 masks init) = poseidon2Perm12 (sumToprfState12 init) := by
  unfold toprfEvalPerm12 poseidon2Perm12
  dsimp only
  rw [sumToprfState12_runExtRounds, sumToprfState12_runIntRounds, sumToprfState12_runExtRounds]
  unfold sumToprfState12
  rw [← applyME_add, ← applyME_add, ← applyME_add, ← applyME_add]

/-- Plaintext Width-12 `Poseidon2` keyed OPRF core `F(k, x)` (`voprf.rs:530-535`):
    rate `b0 = input`, domain/padding `b1 = [1, 0, 0, 0x544f50524631]`, capacity `b2 = key`,
    squeezing the 4-limb (`256`-bit) rate output `b0`. -/
@[expose] def toprfPlaintext (key input : Lane4) : Lane4 :=
  let padLane : Lane4 :=
    ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.ofNat 0x544f50524631⟩
  (poseidon2Perm12 ⟨input, padLane, key⟩).b0

/-- Initialize the 5-component replicated TOPRF state from shared `inputWire` and `keyWire` (`voprf.rs:529-535`). -/
def toprfInitPrfState (keyShares inputShares : Fin 5 → Lane4) : ToprfState12 :=
  let padLane : Lane4 :=
    ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.ofNat 0x544f50524631⟩
  fun c => ⟨inputShares c, if c = 0 then padLane else lane4Zero, keyShares c⟩

def sumLane4Shares5 (sh : Fin 5 → Lane4) : Lane4 :=
  lane4Add (lane4Add (lane4Add (lane4Add (sh 0) (sh 1)) (sh 2)) (sh 3)) (sh 4)

theorem toprfEvalPrf_sum (masks : ToprfPerm12Masks) (keyShares inputShares : Fin 5 → Lane4) :
    (sumToprfState12 (toprfEvalPerm12 masks (toprfInitPrfState keyShares inputShares))).b0 =
      toprfPlaintext (sumLane4Shares5 keyShares) (sumLane4Shares5 inputShares) := by
  rw [toprfEvalPerm12_sum]
  unfold toprfPlaintext
  dsimp only
  have hInit :
      sumToprfState12 (toprfInitPrfState keyShares inputShares) =
        ⟨sumLane4Shares5 inputShares,
         ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.ofNat 0x544f50524631⟩,
         sumLane4Shares5 keyShares⟩ := by
    unfold sumToprfState12 toprfInitPrfState sumLane4Shares5
    have h1 : (1 : Fin 5) ≠ 0 := by decide
    have h2 : (2 : Fin 5) ≠ 0 := by decide
    have h3 : (3 : Fin 5) ≠ 0 := by decide
    have h4 : (4 : Fin 5) ≠ 0 := by decide
    simp only [state12Add_eq, ↓reduceIte, h1, h2, h3, h4, lane4Zero_eq, lane4Add_eq]
    have hAddZ : ∀ x : Goldilocks, Goldilocks.add x Goldilocks.zero = x := LawfulCommRing.add_zero
    simp only [hAddZ]
  rw [hInit]

/-! ### §3.3 1-Byzantine Reshare & Finalize Error-Correction (`toprf_2of5_corrects_one_malicious_server`) -/

/-- 2-of-3 majority decoder on `Option α` where `none` models malformed/omitted erasures (`toprf_engine.rs:183-189`). -/
def majority2Of3 {α : Type} [DecidableEq α] (m0 m1 m2 : Option α) : Option α :=
  match m0, m1, m2 with
  | some v0, some v1, _ => if v0 = v1 then some v0 else
      match m2 with
      | some v2 => if v0 = v2 then some v0 else if v1 = v2 then some v1 else none
      | none => none
  | some v0, none, some v2 => if v0 = v2 then some v0 else none
  | none, some v1, some v2 => if v1 = v2 then some v1 else none
  | _, _, _ => none

theorem majority2Of3_of_two_honest {α : Type} [DecidableEq α] (honest : α)
    (m0 m1 m2 : Option α)
    (hTwo : (m0 = some honest ∧ m1 = some honest) ∨
            (m0 = some honest ∧ m2 = some honest) ∨
            (m1 = some honest ∧ m2 = some honest)) :
    majority2Of3 m0 m1 m2 = some honest := by
  rcases hTwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [majority2Of3]
  · cases m1 with
    | none => simp [majority2Of3]
    | some v1 =>
      unfold majority2Of3
      by_cases hv : honest = v1 <;> simp [hv]
  · cases m0 with
    | none => simp [majority2Of3]
    | some v0 =>
      unfold majority2Of3
      by_cases hv : v0 = honest
      · subst hv; simp
      · simp [hv]

/-- Canonical 8-byte little-endian serialization of a `Goldilocks` vector (`toprf_engine.rs:62-64, 119-122`). -/
def encodeGoldilocksVecLe : List Goldilocks → List UInt8
  | [] => []
  | x :: xs => encodeNatLeBytes 8 x.val ++ encodeGoldilocksVecLe xs

theorem encodeGoldilocksVecLe_length (xs : List Goldilocks) :
    (encodeGoldilocksVecLe xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [encodeGoldilocksVecLe, List.length_append, List.length_cons, encodeNatLeBytes_length, ih]
    omega

theorem encodeGoldilocksVecLe_injective :
    ∀ {xs ys : List Goldilocks},
      encodeGoldilocksVecLe xs = encodeGoldilocksVecLe ys → xs = ys
  | [], [], _ => rfl
  | [], y :: ys, h => by
    have hL := congrArg List.length h
    rw [encodeGoldilocksVecLe_length, encodeGoldilocksVecLe_length] at hL
    simp at hL
  | x :: xs, [], h => by
    have hL := congrArg List.length h
    rw [encodeGoldilocksVecLe_length, encodeGoldilocksVecLe_length] at hL
    simp at hL
  | x :: xs, y :: ys, h => by
    simp only [encodeGoldilocksVecLe] at h
    have hLen8 : (encodeNatLeBytes 8 x.val).length = (encodeNatLeBytes 8 y.val).length := by
      rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
    obtain ⟨hHead, hTail⟩ := append_inj_of_eq_len hLen8 h
    have hxPow : x.val < 256 ^ 8 := Nat.lt_trans x.isLt (by decide)
    have hyPow : y.val < 256 ^ 8 := Nat.lt_trans y.isLt (by decide)
    have hVal : x.val = y.val := by
      have hd := congrArg decodeNatLeBytes hHead
      rwa [decodeNatLeBytes_encodeNatLeBytes 8 x.val hxPow,
           decodeNatLeBytes_encodeNatLeBytes 8 y.val hyPow] at hd
    rw [Goldilocks.ext hVal, encodeGoldilocksVecLe_injective hTail]

/-- Domain tag `"QSAG.TOPRF.RESHARE.DIGEST.V2"` (`toprf_engine.rs:124`, 28 bytes). -/
def toprfReshareDigestTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4F, 0x50, 0x52, 0x46, 0x2E, 0x52, 0x45, 0x53,
   0x48, 0x41, 0x52, 0x45, 0x2E, 0x44, 0x49, 0x47, 0x45, 0x53, 0x54, 0x2E, 0x56, 0x32]

/-- Exact `cshake256_framed_32(b"QSAG.TOPRF.RESHARE.DIGEST.V2", &[context, &layer.to_le_bytes(), &[i, j], &payload])`
    sponge preimage (`toprf_engine.rs:118-127`). -/
def toprfGroupDigestPreimage (ctx : List UInt8) (layer : UInt64) (i j : Fin 5)
    (vals : List Goldilocks) : List UInt8 :=
  cshake256FramedPreimage toprfReshareDigestTag
    [ctx, FixedCodec.u64le.encode layer, [UInt8.ofNat i.val, UInt8.ofNat j.val],
     encodeGoldilocksVecLe vals]

def toprfGroupDigest (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (i j : Fin 5) (vals : List Goldilocks) : List UInt8 :=
  H (toprfGroupDigestPreimage ctx layer i j vals)

/-- Mode A (`gates ≤ 4`, `toprf_engine.rs:183-194`): 3-vector majority decoding over the 3 holders of `(i, j)`. -/
def decodeGroupSmall (m0 m1 m2 : Option (List Goldilocks)) : Option (List Goldilocks) :=
  majority2Of3 m0 m1 m2

/-- Mode B (`gates > 4`, `toprf_engine.rs:195-213`): 2-vector (`m0, m1`) + 1-digest (`md`) decoding!
    Accepts iff `m0 = some v ∧ m1 = some v` OR `md = some d` matches `m0` (checked first) or `m1`. -/
def decodeGroupLarge (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (i j : Fin 5) (m0 m1 : Option (List Goldilocks)) (md : Option (List UInt8)) :
    Option (List Goldilocks) :=
  match m0, m1 with
  | some v0, some v1 =>
    if v0 = v1 then some v0
    else
      match md with
      | some d =>
        if toprfGroupDigest H ctx layer i j v0 = d then some v0
        else if toprfGroupDigest H ctx layer i j v1 = d then some v1
        else none
      | none => none
  | some v0, none =>
    match md with
    | some d => if toprfGroupDigest H ctx layer i j v0 = d then some v0 else none
    | none => none
  | none, some v1 =>
    match md with
    | some d => if toprfGroupDigest H ctx layer i j v1 = d then some v1 else none
    | none => none
  | none, none => none

/-- 3-of-4 client output component majority (`voprf.rs:593-610`): accepts `v` iff `≥ 3` of the 4 component
    holders submit `some v` (`none` models missing/malformed/wrong-context server responses). -/
def majority3Of4 {α : Type} [DecidableEq α] (c0 c1 c2 c3 : Option α) : Option α :=
  let list := [c0, c1, c2, c3]
  let count (v : α) : Nat := (list.filter (fun x => decide (x = some v))).length
  match c0 with
  | some v => if 3 ≤ count v then some v else
      match c1 with
      | some v1 => if 3 ≤ count v1 then some v1 else none
      | none => none
  | none =>
    match c1 with
    | some v1 => if 3 ≤ count v1 then some v1 else none
    | none => none

theorem majority3Of4_of_three_honest {α : Type} [DecidableEq α] (honest : α)
    (c0 c1 c2 c3 : Option α)
    (hThree :
      (c1 = some honest ∧ c2 = some honest ∧ c3 = some honest) ∨
      (c0 = some honest ∧ c2 = some honest ∧ c3 = some honest) ∨
      (c0 = some honest ∧ c1 = some honest ∧ c3 = some honest) ∨
      (c0 = some honest ∧ c1 = some honest ∧ c2 = some honest)) :
    majority3Of4 c0 c1 c2 c3 = some honest := by
  rcases hThree with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · cases c0 with
    | none => simp [majority3Of4]
    | some v0 =>
      unfold majority3Of4
      by_cases hv : v0 = honest
      · subst hv; simp
      · have hne : some honest ≠ some v0 := fun h => hv (Option.some.inj h).symm
        simp [hv, hne]
  · cases c1 with
    | none => simp [majority3Of4]
    | some v1 =>
      unfold majority3Of4
      by_cases hv : v1 = honest <;> simp [hv]
  · cases c2 with
    | none => simp [majority3Of4]
    | some v2 =>
      unfold majority3Of4
      by_cases hv : v2 = honest <;> simp [hv]
  · cases c3 with
    | none => simp [majority3Of4]
    | some v3 =>
      unfold majority3Of4
      by_cases hv : v3 = honest <;> simp [hv]

/-- Client 3-of-4 finalization across all 5 components of a `Lane4` output (`voprf.rs:586-633`). -/
def clientFinalizeLane4 (serverOut : Fin 5 → Option (Fin 5 → Lane4)) : Option Lane4 :=
  let decodeComp (c : Fin 5) : Option Lane4 :=
    match fin5Others c with
    | [p0, p1, p2, p3] =>
      majority3Of4
        ((serverOut p0).map (fun f => f c))
        ((serverOut p1).map (fun f => f c))
        ((serverOut p2).map (fun f => f c))
        ((serverOut p3).map (fun f => f c))
    | _ => none
  match decodeComp 0, decodeComp 1, decodeComp 2, decodeComp 3, decodeComp 4 with
  | some s0, some s1, some s2, some s3, some s4 =>
    some (lane4Add (lane4Add (lane4Add (lane4Add s0 s1) s2) s3) s4)
  | _, _, _, _, _ => none

private theorem fin5_four_others_three_honest (c bad : Fin 5) :
    match fin5Others c with
    | [p0, p1, p2, p3] =>
      (p1 ≠ bad ∧ p2 ≠ bad ∧ p3 ≠ bad) ∨
      (p0 ≠ bad ∧ p2 ≠ bad ∧ p3 ≠ bad) ∨
      (p0 ≠ bad ∧ p1 ≠ bad ∧ p3 ≠ bad) ∨
      (p0 ≠ bad ∧ p1 ≠ bad ∧ p2 ≠ bad)
    | _ => False := by
  have hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
    revert c; decide
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · rw [fin5Others_0]; dsimp only; revert bad; decide
  · rw [fin5Others_1]; dsimp only; revert bad; decide
  · rw [fin5Others_2]; dsimp only; revert bad; decide
  · rw [fin5Others_3]; dsimp only; revert bad; decide
  · rw [fin5Others_4]; dsimp only; revert bad; decide

/-- **Flagship §3.3 Theorem — 1-Byzantine TOPRF Reshare & Finalize Error Correction
    (`toprf_2of5_corrects_one_malicious_server`, `P0-08`–`P0-09`)**:
    Against ANY single malicious/Byzantine server `bad : Fin 5` injecting arbitrary forged values,
    corrupted digests, or missing/truncated erasures (`none`):
    1. **Small-Layer 3-Vector Majority (`gates ≤ 4`, `decodeGroupSmall`):** For any 3 distinct holders
       `(h0, h1, h2)` (`h0 ≠ h1, h0 ≠ h2, h1 ≠ h2`), `decodeGroupSmall` **unconditionally** recovers
       `some honestVec` with zero cryptographic assumptions!
    2. **Large-Layer 2-Vector + 1-Digest (`gates > 4`, `decodeGroupLarge`):** For any 3 distinct holders
       `(hv0, hv1, hd)`, EITHER `decodeGroupLarge` recovers `some honestVec`, OR `bad = hv0` forged a
       distinct `forgedVec ≠ honestVec` exhibiting a length-framed `QSAG.TOPRF.RESHARE.DIGEST.V2` hash collision!
    3. **Client 3-of-4 Finalize (`clientFinalizeLane4`):** Conditional on correct honest engine outputs.
       `toprfActiveClient204_correct` below derives these outputs for the full-value transport. -/
theorem toprf_2of5_corrects_one_malicious_server
    (H : List UInt8 → List UInt8)
    (ctx : List UInt8) (layer : UInt64) (i j : Fin 5)
    (hCtx : ctx.length < 2 ^ 20)
    (bad : Fin 5) :
    -- (1) Small-layer 3-vector majority unconditionally corrects 1 Byzantine server:
    (∀ (h0 h1 h2 : Fin 5) (honestVec : List Goldilocks)
       (m0 m1 m2 : Option (List Goldilocks)),
      h0 ≠ h1 → h0 ≠ h2 → h1 ≠ h2 →
      (h0 ≠ bad → m0 = some honestVec) →
      (h1 ≠ bad → m1 = some honestVec) →
      (h2 ≠ bad → m2 = some honestVec) →
      decodeGroupSmall m0 m1 m2 = some honestVec) ∧
    -- (2) Large-layer 2-vector + 1-digest recovers `some honestVec` OR exhibits an explicit hash collision:
    (∀ (hv0 hv1 hd : Fin 5) (honestVec : List Goldilocks)
       (m0 m1 : Option (List Goldilocks)) (md : Option (List UInt8)),
      hv0 ≠ hv1 → hv0 ≠ hd → hv1 ≠ hd →
      honestVec.length < 2 ^ 20 →
      (∀ v0, m0 = some v0 → v0.length < 2 ^ 20) →
      (hv0 ≠ bad → m0 = some honestVec) →
      (hv1 ≠ bad → m1 = some honestVec) →
      (hd ≠ bad → md = some (toprfGroupDigest H ctx layer i j honestVec)) →
      decodeGroupLarge H ctx layer i j m0 m1 md = some honestVec ∨
        ∃ forgedVec : List Goldilocks,
          m0 = some forgedVec ∧
          forgedVec ≠ honestVec ∧
          toprfGroupDigestPreimage ctx layer i j forgedVec ≠
            toprfGroupDigestPreimage ctx layer i j honestVec ∧
          H (toprfGroupDigestPreimage ctx layer i j forgedVec) =
            H (toprfGroupDigestPreimage ctx layer i j honestVec)) ∧
    -- (3) Client finalization conditional on honest engine outputs:
    (∀ (masks : ToprfPerm12Masks) (keyShares inputShares : Fin 5 → Lane4)
       (serverOut : Fin 5 → Option (Fin 5 → Lane4)),
      (∀ p : Fin 5, p ≠ bad →
        serverOut p = some (fun c => (toprfEvalPerm12 masks (toprfInitPrfState keyShares inputShares) c).b0)) →
      clientFinalizeLane4 serverOut =
        some (toprfPlaintext (sumLane4Shares5 keyShares) (sumLane4Shares5 inputShares))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0 h1 h2 honestVec m0 m1 m2 h01 h02 h12 hm0 hm1 hm2
    unfold decodeGroupSmall
    apply majority2Of3_of_two_honest
    if hb0 : h0 = bad then
      subst hb0
      exact Or.inr (Or.inr ⟨hm1 (Ne.symm h01), hm2 (Ne.symm h02)⟩)
    else if hb1 : h1 = bad then
      subst hb1
      exact Or.inr (Or.inl ⟨hm0 hb0, hm2 (Ne.symm h12)⟩)
    else
      exact Or.inl ⟨hm0 hb0, hm1 hb1⟩
  · intro hv0 hv1 hd honestVec m0 m1 md h01 h0d h1d hLenH hLenM0 hm0 hm1 hmd
    if hb0 : hv0 = bad then
      subst hb0
      have hm1Eq : m1 = some honestVec := hm1 (Ne.symm h01)
      have hmdEq : md = some (toprfGroupDigest H ctx layer i j honestVec) := hmd (Ne.symm h0d)
      rw [hm1Eq, hmdEq]
      cases hm0Case : m0 with
      | none =>
        left
        simp [decodeGroupLarge]
      | some v0 =>
        if hvEq : v0 = honestVec then
          subst hvEq
          left
          simp [decodeGroupLarge]
        else
          if hDigEq : toprfGroupDigest H ctx layer i j v0 = toprfGroupDigest H ctx layer i j honestVec then
            right
            refine ⟨v0, rfl, hvEq, ?_, hDigEq⟩
            intro hPreEq
            unfold toprfGroupDigestPreimage at hPreEq
            have hV0Lt : v0.length < 2 ^ 20 := hLenM0 v0 hm0Case
            have hAll1 : ∀ x ∈ [ctx, FixedCodec.u64le.encode layer, [UInt8.ofNat i.val, UInt8.ofNat j.val],
                                encodeGoldilocksVecLe v0], x.length < 256 ^ 8 := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx1
              · omega
              · rcases List.mem_cons.mp hx1 with rfl | hx2
                · rw [FixedCodec.u64le.encode_len]; decide
                · rcases List.mem_cons.mp hx2 with rfl | hx3
                  · dsimp only [List.length_cons, List.length_nil]; decide
                  · rcases List.mem_cons.mp hx3 with rfl | hx4
                    · rw [encodeGoldilocksVecLe_length]; omega
                    · cases hx4
            have hAll2 : ∀ y ∈ [ctx, FixedCodec.u64le.encode layer, [UInt8.ofNat i.val, UInt8.ofNat j.val],
                                encodeGoldilocksVecLe honestVec], y.length < 256 ^ 8 := by
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy1
              · omega
              · rcases List.mem_cons.mp hy1 with rfl | hy2
                · rw [FixedCodec.u64le.encode_len]; decide
                · rcases List.mem_cons.mp hy2 with rfl | hy3
                  · dsimp only [List.length_cons, List.length_nil]; decide
                  · rcases List.mem_cons.mp hy3 with rfl | hy4
                    · rw [encodeGoldilocksVecLe_length]; omega
                    · cases hy4
            have hListEq := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hPreEq
            injection hListEq with _ t1
            injection t1 with _ t2
            injection t2 with _ t3
            injection t3 with hVecBytes _
            exact hvEq (encodeGoldilocksVecLe_injective hVecBytes)
          else
            left
            simp [decodeGroupLarge, hvEq, hDigEq]
    else if hb1 : hv1 = bad then
      subst hb1
      left
      have hm0Eq : m0 = some honestVec := hm0 hb0
      have hmdEq : md = some (toprfGroupDigest H ctx layer i j honestVec) := hmd (Ne.symm h1d)
      rw [hm0Eq, hmdEq]
      cases m1 with
      | none => simp [decodeGroupLarge]
      | some v1 =>
        unfold decodeGroupLarge
        by_cases hv : honestVec = v1 <;> simp [hv]
    else
      left
      rw [hm0 hb0, hm1 hb1]
      simp [decodeGroupLarge]
  · intro masks keyShares inputShares serverOut hHonestOut
    let evalSt := toprfEvalPerm12 masks (toprfInitPrfState keyShares inputShares)
    have hComp : ∀ c : Fin 5,
        (match fin5Others c with
         | [p0, p1, p2, p3] =>
           majority3Of4
             ((serverOut p0).map (fun f => f c))
             ((serverOut p1).map (fun f => f c))
             ((serverOut p2).map (fun f => f c))
             ((serverOut p3).map (fun f => f c))
         | _ => none) = some (evalSt c).b0 := by
      intro c
      have h3 := fin5_four_others_three_honest c bad
      cases hOthers : fin5Others c with
      | nil => rw [hOthers] at h3; exact False.elim h3
      | cons p0 r0 =>
        cases r0 with
        | nil => rw [hOthers] at h3; exact False.elim h3
        | cons p1 r1 =>
          cases r1 with
          | nil => rw [hOthers] at h3; exact False.elim h3
          | cons p2 r2 =>
            cases r2 with
            | nil => rw [hOthers] at h3; exact False.elim h3
            | cons p3 r3 =>
              cases r3 with
              | cons _ _ => rw [hOthers] at h3; exact False.elim h3
              | nil =>
                rw [hOthers] at h3
                apply majority3Of4_of_three_honest
                rcases h3 with ⟨n1, n2, n3⟩ | ⟨n0, n2, n3⟩ | ⟨n0, n1, n3⟩ | ⟨n0, n1, n2⟩
                · exact Or.inl ⟨by rw [hHonestOut p1 n1]; rfl,
                                by rw [hHonestOut p2 n2]; rfl,
                                by rw [hHonestOut p3 n3]; rfl⟩
                · exact Or.inr (Or.inl ⟨by rw [hHonestOut p0 n0]; rfl,
                                        by rw [hHonestOut p2 n2]; rfl,
                                        by rw [hHonestOut p3 n3]; rfl⟩)
                · exact Or.inr (Or.inr (Or.inl ⟨by rw [hHonestOut p0 n0]; rfl,
                                                by rw [hHonestOut p1 n1]; rfl,
                                                by rw [hHonestOut p3 n3]; rfl⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨by rw [hHonestOut p0 n0]; rfl,
                                                by rw [hHonestOut p1 n1]; rfl,
                                                by rw [hHonestOut p2 n2]; rfl⟩))
    unfold clientFinalizeLane4
    dsimp only
    rw [hComp 0, hComp 1, hComp 2, hComp 3, hComp 4]
    dsimp only
    apply congrArg some
    have hPrf := toprfEvalPrf_sum masks keyShares inputShares
    rw [sumToprfState12_lanes] at hPrf
    dsimp only at hPrf
    simp only [lane4Add_eq, sumWire5] at hPrf ⊢
    exact hPrf

/-- **`#tooth` (`tooth_toprf_two_corrupt_servers_can_forge_majority`)**:
    When 2 servers (`bad1 = 1, bad2 = 2`) collude among the 3 cross-term holders `toprfHolders 0 4 = [1, 2, 3]`
    (violating the $t' = 1$ Byzantine corruption bound of 2-of-5 TOPRF), BOTH `decodeGroupSmall` AND
    `decodeGroupLarge` (even under an injective identity hash `H = id`!) silently accept `forgedVec ≠ honestVec`! -/
theorem tooth_toprf_two_corrupt_servers_can_forge_majority :
    let honestVec : List Goldilocks := [Goldilocks.zero]
    let forgedVec : List Goldilocks := [Goldilocks.one]
    toprfHolders 0 4 = [1, 2, 3] ∧
    forgedVec ≠ honestVec ∧
    decodeGroupSmall (some forgedVec) (some forgedVec) (some honestVec) = some forgedVec ∧
    decodeGroupLarge id [0x07] 0 0 4 (some forgedVec) (some forgedVec)
      (some (toprfGroupDigest id [0x07] 0 0 4 honestVec)) = some forgedVec := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro h
    injection h with h10
    have hv := congrArg Goldilocks.val h10
    simp at hv
  · simp [decodeGroupSmall, majority2Of3]
  · simp [decodeGroupLarge]

/-- Non-vacuous inhabitedness witness for 2-of-5 TOPRF correcting an omitted/corrupt server response. -/
theorem toprf_2of5_inhabited :
    ∃ (masks : ToprfPerm12Masks) (keyShares inputShares : Fin 5 → Lane4)
      (serverOut : Fin 5 → Option (Fin 5 → Lane4)),
      serverOut 0 = none ∧
      (∀ p : Fin 5, p ≠ 0 →
        serverOut p = some (fun c => (toprfEvalPerm12 masks (toprfInitPrfState keyShares inputShares) c).b0)) ∧
      clientFinalizeLane4 serverOut =
        some (toprfPlaintext (sumLane4Shares5 keyShares) (sumLane4Shares5 inputShares)) := by
  let zMask : SboxMask4 := {
    m1 := fun _ _ => Goldilocks.zero
    m2 := fun _ _ => Goldilocks.zero
    m3 := fun _ _ => Goldilocks.zero
    m4 := fun _ _ => Goldilocks.zero
  }
  let masks : ToprfPerm12Masks := {
    initExt := fun _ _ => zMask
    internal := fun _ => zMask
    termExt := fun _ _ => zMask
  }
  let kSh : Fin 5 → Lane4 := fun _ => lane4Zero
  let iSh : Fin 5 → Lane4 := fun _ => lane4Zero
  let evalSt := toprfEvalPerm12 masks (toprfInitPrfState kSh iSh)
  let serverOut : Fin 5 → Option (Fin 5 → Lane4) :=
    fun p => if p = 0 then none else some (fun c => (evalSt c).b0)
  have hHon : ∀ p : Fin 5, p ≠ 0 →
      serverOut p = some (fun c => (toprfEvalPerm12 masks (toprfInitPrfState kSh iSh) c).b0) :=
    fun p hp => by simp [serverOut, evalSt, hp]
  refine ⟨masks, kSh, iSh, serverOut, rfl, hHon, ?_⟩
  exact (toprf_2of5_corrects_one_malicious_server id [] 0 0 1 (by decide) 0).2.2 masks kSh iSh serverOut hHon

/-! ### §3.4 1-Curious-Server Privacy (`toprf_one_curious_server_hiding`) & Input-Root Binding -/

abbrev GoldQuad := Goldilocks × Goldilocks × Goldilocks × Goldilocks

/-- Client 5-component share encoding of `val` from 4 uniform coins `r = (r0, r1, r2, r3)` (`voprf.rs:423-426`). -/
def clientShareWire (val : Goldilocks) (r : GoldQuad) : ToprfWire
  | 0 => r.1
  | 1 => r.2.1
  | 2 => r.2.2.1
  | 3 => r.2.2.2
  | 4 => Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val r.1) r.2.1) r.2.2.1) r.2.2.2

/-- The 4 shares `(w c)_{c ≠ p}` delivered to server `p` (`voprf.rs:427-433`: component `p` is zeroed/omitted!). -/
def clientViewAtServer (p : Fin 5) (w : ToprfWire) : GoldQuad :=
  match p with
  | ⟨0, _⟩ => (w 1, w 2, w 3, w 4)
  | ⟨1, _⟩ => (w 0, w 2, w 3, w 4)
  | ⟨2, _⟩ => (w 0, w 1, w 3, w 4)
  | ⟨3, _⟩ => (w 0, w 1, w 2, w 4)
  | ⟨4, _⟩ => (w 0, w 1, w 2, w 3)

/-- Explicit inverse recovering the 4 client sharing coins `r` from server `p`'s observed 4-share view `v`. -/
def clientCoinsFromServerView (p : Fin 5) (val : Goldilocks) (v : GoldQuad) : GoldQuad :=
  let missing := Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val v.1) v.2.1) v.2.2.1) v.2.2.2
  match p with
  | ⟨0, _⟩ => (missing, v.1, v.2.1, v.2.2.1)
  | ⟨1, _⟩ => (v.1, missing, v.2.1, v.2.2.1)
  | ⟨2, _⟩ => (v.1, v.2.1, missing, v.2.2.1)
  | ⟨3, _⟩ => (v.1, v.2.1, v.2.2.1, missing)
  | ⟨4, _⟩ => v

/-- Per-gate incoming view `(t_0 - r_0, t_1 - r_1, t_2 - r_2, t_3 - r_3)` received by server `p` (`toprf_engine.rs:17-20`). -/
def serverGateMaskedView (terms masks : GoldQuad) : GoldQuad :=
  (Goldilocks.sub terms.1 masks.1,
   Goldilocks.sub terms.2.1 masks.2.1,
   Goldilocks.sub terms.2.2.1 masks.2.2.1,
   Goldilocks.sub terms.2.2.2 masks.2.2.2)

private theorem gold_sub_sub_self (t r : Goldilocks) :
    Goldilocks.sub t (Goldilocks.sub t r) = r := by
  rw [← goldOfInt_nat t, ← goldOfInt_nat r]
  simp only [goldOfInt_sub]
  congr 1; omega

/-- **Flagship §3.4a Theorem — 1-Curious-Server Input & Gate-View Hiding (`toprf_one_curious_server_hiding`)**:
    For EVERY single curious server `p : Fin 5`:
    1. `sumWire5 (clientShareWire val r) = val` for all `val` and coins `r`;
    2. There is an explicit `SimpleEquiv GoldQuad GoldQuad` between uniform client coins `r` and server `p`'s
       observed 4-component share view `clientViewAtServer p (clientShareWire val r)` — hence for ANY two
       client inputs `valA, valB : Goldilocks`, composing `(equiv p valB)⁻¹ ∘ (equiv p valA)` gives a
       constructive coin bijection producing **identical** views at server `p`!
    3. Per multiplication gate, `serverGateMaskedView terms` is a self-inverse `SimpleEquiv GoldQuad GoldQuad`
       mapping the 4 masks derived from `seed(p, p)` (the unique seed missing from server `p`!) onto server `p`'s
       4 incoming cross-term messages! -/
theorem toprf_one_curious_server_hiding :
    (∀ (val : Goldilocks) (r : GoldQuad), sumWire5 (clientShareWire val r) = val) ∧
    (∀ (p : Fin 5) (val : Goldilocks),
      ∃ eqv : SimpleEquiv GoldQuad GoldQuad,
        (∀ r : GoldQuad, eqv.toFun r = clientViewAtServer p (clientShareWire val r))) ∧
    (∀ (terms : GoldQuad),
      ∃ eqv : SimpleEquiv GoldQuad GoldQuad,
        (∀ masks : GoldQuad, eqv.toFun masks = serverGateMaskedView terms masks) ∧
        (∀ view : GoldQuad, eqv.invFun view = serverGateMaskedView terms view)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro val ⟨r0, r1, r2, r3⟩
    unfold sumWire5 clientShareWire
    dsimp only
    rw [← goldOfInt_nat val, ← goldOfInt_nat r0, ← goldOfInt_nat r1,
        ← goldOfInt_nat r2, ← goldOfInt_nat r3]
    simp only [goldOfInt_add, goldOfInt_sub]
    congr 1; omega
  · intro p val
    have hSub4_0 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val b) c) d)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d) = a := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hSub4_1 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) c) d)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d) = b := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hSub4_2 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) d)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d) = c := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hSub4_3 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d) = d := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hRInv_0 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d)) a) b) c = d := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hRInv_1 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d)) b) c = d := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hRInv_2 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d)) c = d := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    refine ⟨{
      toFun := fun r => clientViewAtServer p (clientShareWire val r)
      invFun := clientCoinsFromServerView p val
      left_inv := ?_
      right_inv := ?_
    }, fun _ => rfl⟩
    · intro ⟨r0, r1, r2, r3⟩
      rcases p with ⟨pv, hpv⟩
      have hCases : pv = 0 ∨ pv = 1 ∨ pv = 2 ∨ pv = 3 ∨ pv = 4 := by omega
      rcases hCases with rfl | rfl | rfl | rfl | rfl
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hSub4_0]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hSub4_1]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hSub4_2]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hSub4_3]
      · rfl
    · intro ⟨v0, v1, v2, v3⟩
      rcases p with ⟨pv, hpv⟩
      have hCases : pv = 0 ∨ pv = 1 ∨ pv = 2 ∨ pv = 3 ∨ pv = 4 := by omega
      rcases hCases with rfl | rfl | rfl | rfl | rfl
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hRInv_0]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hRInv_1]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hRInv_2]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hSub4_3]
      · rfl
  · intro terms
    refine ⟨{
      toFun := serverGateMaskedView terms
      invFun := serverGateMaskedView terms
      left_inv := fun ⟨m0, m1, m2, m3⟩ => by
        unfold serverGateMaskedView
        dsimp only
        rw [gold_sub_sub_self, gold_sub_sub_self, gold_sub_sub_self, gold_sub_sub_self]
      right_inv := fun ⟨v0, v1, v2, v3⟩ => by
        unfold serverGateMaskedView
        dsimp only
        rw [gold_sub_sub_self, gold_sub_sub_self, gold_sub_sub_self, gold_sub_sub_self]
    }, fun _ => rfl, fun _ => rfl⟩

/-- TOPRF evaluation session context matching `voprf::Context` (`voprf.rs:360-386`). -/
structure ToprfEvalContext where
  key : List UInt8
  session : List UInt8
  counter : UInt64
  items : UInt64
  deriving DecidableEq, Repr

/-- Domain tag `"QSAG.TOPRF.EVAL.V1"` (`voprf.rs:378`, 18 bytes). -/
def toprfEvalContextTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4F, 0x50, 0x52,
   0x46, 0x2E, 0x45, 0x56, 0x41, 0x4C, 0x2E, 0x56, 0x31]

/-- Exact `Context::base_digest()` sponge preimage (`voprf.rs:376-386`):
    `cshake256_framed_32(b"QSAG.TOPRF.EVAL.V1", &[&key, &session, &counter.to_le_bytes(), &items.to_le_bytes()])`. -/
def toprfContextBasePreimage (ctx : ToprfEvalContext) : List UInt8 :=
  cshake256FramedPreimage toprfEvalContextTag
    [ctx.key, ctx.session, FixedCodec.u64le.encode ctx.counter, FixedCodec.u64le.encode ctx.items]

def toprfContextBaseDigest (H : List UInt8 → List UInt8) (ctx : ToprfEvalContext) : List UInt8 :=
  H (toprfContextBasePreimage ctx)

theorem toprfContextBasePreimage_injective {ctx₁ ctx₂ : ToprfEvalContext}
    (hk₁ : ctx₁.key.length < 256 ^ 8) (hs₁ : ctx₁.session.length < 256 ^ 8)
    (hk₂ : ctx₂.key.length < 256 ^ 8) (hs₂ : ctx₂.session.length < 256 ^ 8)
    (hEq : toprfContextBasePreimage ctx₁ = toprfContextBasePreimage ctx₂) :
    ctx₁ = ctx₂ := by
  unfold toprfContextBasePreimage at hEq
  have hAll₁ : ∀ f ∈ [ctx₁.key, ctx₁.session, FixedCodec.u64le.encode ctx₁.counter,
                      FixedCodec.u64le.encode ctx₁.items], f.length < 256 ^ 8 := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | h1
    · exact hk₁
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact hs₁
      · rcases List.mem_cons.mp h2 with rfl | h3
        · rw [FixedCodec.u64le.encode_len]; decide
        · rcases List.mem_cons.mp h3 with rfl | h4
          · rw [FixedCodec.u64le.encode_len]; decide
          · cases h4
  have hAll₂ : ∀ g ∈ [ctx₂.key, ctx₂.session, FixedCodec.u64le.encode ctx₂.counter,
                      FixedCodec.u64le.encode ctx₂.items], g.length < 256 ^ 8 := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | h1
    · exact hk₂
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact hs₂
      · rcases List.mem_cons.mp h2 with rfl | h3
        · rw [FixedCodec.u64le.encode_len]; decide
        · rcases List.mem_cons.mp h3 with rfl | h4
          · rw [FixedCodec.u64le.encode_len]; decide
          · cases h4
  have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll₁ hAll₂ hEq
  injection hFr with eKey t1
  injection t1 with eSes t2
  injection t2 with eCnt t3
  injection t3 with eItm _
  have hCnt : ctx₁.counter = ctx₂.counter := FixedCodec.u64le.encode_injective eCnt
  have hItm : ctx₁.items = ctx₂.items := FixedCodec.u64le.encode_injective eItm
  rcases ctx₁ with ⟨k1, s1, c1, i1⟩
  rcases ctx₂ with ⟨k2, s2, c2, i2⟩
  dsimp only at eKey eSes hCnt hItm
  subst eKey eSes hCnt hItm
  rfl

/-- Domain tag `"QSAG.TOPRF.INPUT.COMMIT.V1"` (`voprf.rs:403`, 26 bytes). -/
def toprfInputCommitTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4F, 0x50, 0x52, 0x46, 0x2E, 0x49, 0x4E,
   0x50, 0x55, 0x54, 0x2E, 0x43, 0x4F, 0x4D, 0x4D, 0x49, 0x54, 0x2E, 0x56, 0x31]

/-- Domain tag `"QSAG.TOPRF.INPUT.BIND.V1"` (`voprf.rs:482, 575`, 24 bytes). -/
def toprfInputBindTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4F, 0x50, 0x52, 0x46, 0x2E, 0x49,
   0x4E, 0x50, 0x55, 0x54, 0x2E, 0x42, 0x49, 0x4E, 0x44, 0x2E, 0x56, 0x31]

/-- Exact `input_commitment(request, component)` sponge preimage (`voprf.rs:395-411`):
    absorbs `[&request.context.base_digest(), &[component as u8], &request.salts[component], &payload]`. -/
def toprfInputCommitPreimage (baseDigest : List UInt8) (c : Fin 5)
    (salt : List UInt8) (shares : List Goldilocks) : List UInt8 :=
  cshake256FramedPreimage toprfInputCommitTag
    [baseDigest, [UInt8.ofNat c.val], salt, encodeGoldilocksVecLe shares]

def toprfInputCommit (H : List UInt8 → List UInt8) (baseDigest : List UInt8) (c : Fin 5)
    (salt : List UInt8) (shares : List Goldilocks) : List UInt8 :=
  H (toprfInputCommitPreimage baseDigest c salt shares)

/-- **`#tooth` (`tooth_omitting_base_digest_allows_cross_session_replay`)**:
    A broken input commitment omitting `context.base_digest()` produces **byte-identical** commitments
    across distinct sessions/counters `ctx₁ ≠ ctx₂` (`rfl`), whereas `toprfContextBasePreimage` strictly
    separates `ctx₁` and `ctx₂` and `toprfInputCommitPreimage` strictly separates any two distinct
    `< 256^8`-byte base digests (including 32-byte `cshake256Bytes` digests)! -/
theorem tooth_omitting_base_digest_allows_cross_session_replay :
    let brokenPreimage (c : Fin 5) (salt : List UInt8) (shares : List Goldilocks) : List UInt8 :=
      cshake256FramedPreimage toprfInputCommitTag [[UInt8.ofNat c.val], salt, encodeGoldilocksVecLe shares]
    let ctx₁ : ToprfEvalContext := { key := [0x11], session := [0xA1], counter := 0, items := 1 }
    let ctx₂ : ToprfEvalContext := { key := [0x11], session := [0xB2], counter := 1, items := 1 }
    let H₀ : List UInt8 → List UInt8 := fun bs =>
      if bs = toprfContextBasePreimage ctx₁ then [0x01] else [0x02]
    ctx₁ ≠ ctx₂ ∧
    toprfContextBasePreimage ctx₁ ≠ toprfContextBasePreimage ctx₂ ∧
    brokenPreimage 0 [0x55] [Goldilocks.one] = brokenPreimage 0 [0x55] [Goldilocks.one] ∧
    toprfInputCommit id (toprfContextBaseDigest H₀ ctx₁) 0 [0x55] [Goldilocks.one] ≠
      toprfInputCommit id (toprfContextBaseDigest H₀ ctx₂) 0 [0x55] [Goldilocks.one] := by
  have hPreNe :
      toprfContextBasePreimage { key := [0x11], session := [0xA1], counter := 0, items := 1 } ≠
        toprfContextBasePreimage { key := [0x11], session := [0xB2], counter := 1, items := 1 } := by
    intro hBaseEq
    have hCtxEq := toprfContextBasePreimage_injective (by simp) (by simp) (by simp) (by simp) hBaseEq
    injection hCtxEq with _ eSes _ _
    cases eSes
  refine ⟨by decide, hPreNe, rfl, ?_⟩
  intro hEq
  dsimp only [toprfInputCommit, toprfContextBaseDigest, id] at hEq
  rw [ite_true_of rfl, ite_false_of (Ne.symm hPreNe)] at hEq
  have hEncLen : (encodeGoldilocksVecLe [Goldilocks.one]).length < 256 ^ 8 := by
    rw [encodeGoldilocksVecLe_length]; decide
  have hAll1 : ∀ f ∈ [([0x01] : List UInt8), [UInt8.ofNat (0 : Fin 5).val], ([0x55] : List UInt8),
                      encodeGoldilocksVecLe [Goldilocks.one]], f.length < 256 ^ 8 := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | t1
    · decide
    · rcases List.mem_cons.mp t1 with rfl | t2
      · decide
      · rcases List.mem_cons.mp t2 with rfl | t3
        · decide
        · rcases List.mem_cons.mp t3 with rfl | t4
          · exact hEncLen
          · cases t4
  have hAll2 : ∀ g ∈ [([0x02] : List UInt8), [UInt8.ofNat (0 : Fin 5).val], ([0x55] : List UInt8),
                      encodeGoldilocksVecLe [Goldilocks.one]], g.length < 256 ^ 8 := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | t1
    · decide
    · rcases List.mem_cons.mp t1 with rfl | t2
      · decide
      · rcases List.mem_cons.mp t2 with rfl | t3
        · decide
        · rcases List.mem_cons.mp t3 with rfl | t4
          · exact hEncLen
          · cases t4
  have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hEq
  injection hFr with eBase _
  cases eBase

/-- 4-holder unanimity check on component `c` (`voprf.rs:511-525`): all 4 servers `p ≠ c` must broadcast
    the identical 32-byte commitment digest `expected`! -/
def checkComponentUnanimity (c : Fin 5) (broadcastDigests : Fin 5 → List UInt8) : Bool :=
  match fin5Others c with
  | [p0, p1, p2, p3] =>
    decide (broadcastDigests p0 = broadcastDigests p1) &&
    decide (broadcastDigests p0 = broadcastDigests p2) &&
    decide (broadcastDigests p0 = broadcastDigests p3)
  | _ => false

/-- Exact `cshake256_framed_32(b"QSAG.TOPRF.INPUT.BIND.V1", &[input])` sponge preimage (`voprf.rs:482, 575`). -/
def toprfInputBindPreimage (input : List UInt8) : List UInt8 :=
  cshake256FramedPreimage toprfInputBindTag [input]

/-- Client `Evaluation::value_for` (`voprf.rs:571-580`): verifies `evalKey = expectedKey` and looks up
    `H (toprfInputBindPreimage queriedInput)` inside the enrolled `inputDigests`. -/
def toprfValueFor (H : List UInt8 → List UInt8)
    (expectedKey evalKey : List UInt8)
    (enrolledInputs : List (List UInt8))
    (values : List (List UInt8))
    (queriedInput : List UInt8) : Option (List UInt8) :=
  if evalKey = expectedKey then
    let target := H (toprfInputBindPreimage queriedInput)
    let rec findIdx : List (List UInt8) → List (List UInt8) → Option (List UInt8)
      | d :: ds, v :: vsl => if d = target then some v else findIdx ds vsl
      | _, _ => none
    findIdx (enrolledInputs.map (fun x => H (toprfInputBindPreimage x))) values
  else
    none

private theorem checkComponentUnanimity_eq_of_mem {c p q : Fin 5}
    {digests : Fin 5 → List UInt8}
    (hUnan : checkComponentUnanimity c digests = true)
    (hp : p ≠ c) (hq : q ≠ c) :
    digests p = digests q := by
  have hPair :
      ∀ (c p q : Fin 5), p ≠ c → q ≠ c →
        match fin5Others c with
        | [p0, p1, p2, p3] =>
          (p = p0 ∨ p = p1 ∨ p = p2 ∨ p = p3) ∧
          (q = p0 ∨ q = p1 ∨ q = p2 ∨ q = p3)
        | _ => False := by
    intro c0
    have hc : c0 = 0 ∨ c0 = 1 ∨ c0 = 2 ∨ c0 = 3 ∨ c0 = 4 := by
      revert c0; decide
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · rw [fin5Others_0]; dsimp only; decide
    · rw [fin5Others_1]; dsimp only; decide
    · rw [fin5Others_2]; dsimp only; decide
    · rw [fin5Others_3]; dsimp only; decide
    · rw [fin5Others_4]; dsimp only; decide
  have hpq := hPair c p q hp hq
  unfold checkComponentUnanimity at hUnan
  cases hOthers : fin5Others c with
  | nil => rw [hOthers] at hpq; exact False.elim hpq
  | cons p0 r0 =>
    cases r0 with
    | nil => rw [hOthers] at hpq; exact False.elim hpq
    | cons p1 r1 =>
      cases r1 with
      | nil => rw [hOthers] at hpq; exact False.elim hpq
      | cons p2 r2 =>
        cases r2 with
        | nil => rw [hOthers] at hpq; exact False.elim hpq
        | cons p3 r3 =>
          cases r3 with
          | cons _ _ => rw [hOthers] at hpq; exact False.elim hpq
          | nil =>
            rw [hOthers] at hUnan hpq
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hUnan
            rcases hUnan with ⟨⟨e01, e02⟩, e03⟩
            rcases hpq with ⟨hpCases, hqCases⟩
            have hpEq0 : digests p = digests p0 := by
              rcases hpCases with rfl | rfl | rfl | rfl
              · rfl
              · exact e01.symm
              · exact e02.symm
              · exact e03.symm
            have hqEq0 : digests q = digests p0 := by
              rcases hqCases with rfl | rfl | rfl | rfl
              · rfl
              · exact e01.symm
              · exact e02.symm
              · exact e03.symm
            exact hpEq0.trans hqEq0.symm

/-- **Flagship §3.4b Theorem — Context-Bound Salted Input-Root Equivocation & Relabeling Security
    (`toprf_input_root_blocks_relabeling_and_equivocation`, `voprf.rs:376-411, 501-580`, fixing `C0-2`)**:
    1. **4-Holder Unanimity + `context.base_digest()` Binding**: Whenever a malicious client delivers
       distinct `(ctx₁, salt₁, sh₁) ≠ (ctx₂, salt₂, sh₂)` for component `c` to ANY two honest holders
       `h₁, h₂ ≠ c`, `checkComponentUnanimity` rejects (`= false`) unless `H` collides on length-framed
       `"QSAG.TOPRF.EVAL.V1"` (`toprfContextBasePreimage`) or `"QSAG.TOPRF.INPUT.COMMIT.V1"`
       (`toprfInputCommitPreimage`)!
    2. **`#tooth` (Majority vs Unanimity)**: A 3-of-4 majority check allows 1 corrupt server + 2 honest
       servers holding `dA` to outvote honest server `4` holding `dB ≠ dA`!
    3. **Input-Binding Blocks Cross-Input Output Relabeling**: Querying `toprfValueFor` on any `queried ∉ enrolled`
       returns `none` unless `H` collides on length-framed `"QSAG.TOPRF.INPUT.BIND.V1"`! -/
theorem toprf_input_root_blocks_relabeling_and_equivocation
    (H : List UInt8 → List UInt8) :
    (∀ (c h₁ h₂ : Fin 5) (ctx₁ ctx₂ : ToprfEvalContext)
       (salt₁ salt₂ : List UInt8) (sh₁ sh₂ : List Goldilocks)
       (digests : Fin 5 → List UInt8),
      h₁ ≠ c → h₂ ≠ c →
      ctx₁.key.length < 256 ^ 8 → ctx₁.session.length < 256 ^ 8 →
      ctx₂.key.length < 256 ^ 8 → ctx₂.session.length < 256 ^ 8 →
      (toprfContextBaseDigest H ctx₁).length < 256 ^ 8 →
      (toprfContextBaseDigest H ctx₂).length < 256 ^ 8 →
      salt₁.length < 256 ^ 8 → salt₂.length < 256 ^ 8 →
      sh₁.length < 2 ^ 56 → sh₂.length < 2 ^ 56 →
      (ctx₁, salt₁, sh₁) ≠ (ctx₂, salt₂, sh₂) →
      digests h₁ = toprfInputCommit H (toprfContextBaseDigest H ctx₁) c salt₁ sh₁ →
      digests h₂ = toprfInputCommit H (toprfContextBaseDigest H ctx₂) c salt₂ sh₂ →
      checkComponentUnanimity c digests = false ∨
        (toprfContextBasePreimage ctx₁ ≠ toprfContextBasePreimage ctx₂ ∧
         H (toprfContextBasePreimage ctx₁) = H (toprfContextBasePreimage ctx₂)) ∨
        (toprfInputCommitPreimage (toprfContextBaseDigest H ctx₁) c salt₁ sh₁ ≠
           toprfInputCommitPreimage (toprfContextBaseDigest H ctx₂) c salt₂ sh₂ ∧
         H (toprfInputCommitPreimage (toprfContextBaseDigest H ctx₁) c salt₁ sh₁) =
           H (toprfInputCommitPreimage (toprfContextBaseDigest H ctx₂) c salt₂ sh₂))) ∧
    (majority3Of4 (some ([0x01] : List UInt8)) (some [0x01]) (some [0x01]) (some [0x02]) = some [0x01] ∧
     checkComponentUnanimity 0 (fun p => if p = 4 then [0x02] else [0x01]) = false) ∧
    (∀ (expectedKey evalKey queried : List UInt8) (enrolled values : List (List UInt8)),
      queried.length < 256 ^ 8 →
      (∀ x ∈ enrolled, x.length < 256 ^ 8) →
      queried ∉ enrolled →
      toprfValueFor H expectedKey evalKey enrolled values queried = none ∨
        ∃ x ∈ enrolled,
          toprfInputBindPreimage x ≠ toprfInputBindPreimage queried ∧
          H (toprfInputBindPreimage x) = H (toprfInputBindPreimage queried)) := by
  refine ⟨?_, ⟨by decide, by decide⟩, ?_⟩
  · intro c h₁ h₂ ctx₁ ctx₂ salt₁ salt₂ sh₁ sh₂ digests hh1 hh2 hk1 hs1 hk2 hs2 hbd1 hbd2 hslt1 hslt2 hsh1 hsh2 hNe hd1 hd2
    cases hUnan : checkComponentUnanimity c digests with
    | false => exact Or.inl rfl
    | true =>
      have hDigEq := checkComponentUnanimity_eq_of_mem hUnan hh1 hh2
      rw [hd1, hd2] at hDigEq
      let bd₁ := toprfContextBaseDigest H ctx₁
      let bd₂ := toprfContextBaseDigest H ctx₂
      if hPreEq : toprfInputCommitPreimage bd₁ c salt₁ sh₁ = toprfInputCommitPreimage bd₂ c salt₂ sh₂ then
        have hAll1 : ∀ f ∈ [bd₁, [UInt8.ofNat c.val], salt₁, encodeGoldilocksVecLe sh₁], f.length < 256 ^ 8 := by
          intro f hf
          rcases List.mem_cons.mp hf with rfl | t1
          · exact hbd1
          · rcases List.mem_cons.mp t1 with rfl | t2
            · dsimp only [List.length_cons, List.length_nil]; decide
            · rcases List.mem_cons.mp t2 with rfl | t3
              · exact hslt1
              · rcases List.mem_cons.mp t3 with rfl | t4
                · rw [encodeGoldilocksVecLe_length]; omega
                · cases t4
        have hAll2 : ∀ g ∈ [bd₂, [UInt8.ofNat c.val], salt₂, encodeGoldilocksVecLe sh₂], g.length < 256 ^ 8 := by
          intro g hg
          rcases List.mem_cons.mp hg with rfl | t1
          · exact hbd2
          · rcases List.mem_cons.mp t1 with rfl | t2
            · dsimp only [List.length_cons, List.length_nil]; decide
            · rcases List.mem_cons.mp t2 with rfl | t3
              · exact hslt2
              · rcases List.mem_cons.mp t3 with rfl | t4
                · rw [encodeGoldilocksVecLe_length]; omega
                · cases t4
        have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hPreEq
        injection hFr with eBd t1
        injection t1 with _ t2
        injection t2 with eSalt t3
        injection t3 with eShBytes _
        have eSh := encodeGoldilocksVecLe_injective eShBytes
        if hCtxEq : ctx₁ = ctx₂ then
          exfalso
          exact hNe (by rw [hCtxEq, eSalt, eSh])
        else
          right; left
          refine ⟨fun hBasePreEq => hCtxEq (toprfContextBasePreimage_injective hk1 hs1 hk2 hs2 hBasePreEq), eBd⟩
      else
        exact Or.inr (Or.inr ⟨hPreEq, hDigEq⟩)
  · intro expectedKey evalKey queried enrolled values hQLen hEnrLen hNotMem
    unfold toprfValueFor
    if hKey : evalKey = expectedKey then
      rw [ite_true_of hKey]
      dsimp only
      induction enrolled generalizing values with
      | nil =>
        left
        cases values <;> rfl
      | cons x xs ih =>
        cases values with
        | nil => left; rfl
        | cons v vsl =>
          dsimp only [List.map, toprfValueFor.findIdx]
          if hHit : H (toprfInputBindPreimage x) = H (toprfInputBindPreimage queried) then
            right
            have hxNeQ : x ≠ queried := fun hEq => hNotMem (hEq ▸ .head xs)
            refine ⟨x, .head xs, ?_, hHit⟩
            intro hPreEq
            unfold toprfInputBindPreimage at hPreEq
            have hxLen : x.length < 256 ^ 8 := hEnrLen x (.head xs)
            have hAll1 : ∀ f ∈ [x], f.length < 256 ^ 8 := by
              intro f hf; rcases List.mem_cons.mp hf with rfl | h0; exact hxLen; cases h0
            have hAll2 : ∀ g ∈ [queried], g.length < 256 ^ 8 := by
              intro g hg; rcases List.mem_cons.mp hg with rfl | h0; exact hQLen; cases h0
            have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hPreEq
            injection hFr with hxEqQ _
            exact hxNeQ hxEqQ
          else
            rw [ite_false_of hHit]
            have ihRes := ih vsl (fun z hz => hEnrLen z (.tail x hz)) (fun hq => hNotMem (.tail x hq))
            rcases ihRes with hNone | ⟨z, hzMem, hPreNe, hCol⟩
            · exact Or.inl hNone
            · exact Or.inr ⟨z, .tail x hzMem, hPreNe, hCol⟩
    else
      rw [ite_false_of hKey]
      exact Or.inl rfl

/-! ## §4. `BlindVC` Rate-6/Capacity-6 6-Limb `absorbRate6Sponge3` Commitment & ZKBoo Selective Disclosure (`blind_vc.rs`, fixing `C0-3` & `C1-2`) -/

/-! ### §4.1 6-Limb `Lane6` Digests, `ZkSoundnessProfile` (ROM vs QROM) & Arity-Framed `absorbRate6Sponge3` Binding -/

/-- Maximum canonical Goldilocks attributes per `BlindVC` credential (`MAX_VC_ATTRS = 6`, `blind_vc.rs:43`). -/
def vcMaxAttrs : Nat := 6

/-- Deployed Poseidon2 Merkle accumulator depth (`VC_ACCUMULATOR_DEPTH = 20`, `blind_vc.rs:45`). -/
def vcAccumulatorDepth : Nat := 20

/-- ZKBoo soundness profile (`ZkSoundnessProfile`, `blind_vc.rs:47, 780-810`, fixing `C1-2`):
    - `.classical128`: `219` repetitions (`(2/3)^219 < 2^{-128}` classical ROM soundness,
      whereas `2^{-130} < (2/3)^219` yields `< 65`-bit security against QROM Grover challenge grinding);
    - `.quantum128`: `438` repetitions (`VC_ZKBOO_REPS = 438`, default post-quantum profile:
      `(2/3)^438 < 2^{-256}`, sustaining `≥ 128`-bit QROM soundness against $O(2^{k/2})$ Grover
      amplitude amplification over Fiat-Shamir challenge grinding). -/
inductive ZkSoundnessProfile where
  | classical128
  | quantum128
  deriving DecidableEq, Repr

def ZkSoundnessProfile.repetitions : ZkSoundnessProfile → Nat
  | .classical128 => 219
  | .quantum128 => 438

/-- Default post-quantum ZKBoo repetition count (`VC_ZKBOO_REPS = 438`, `blind_vc.rs:47`). -/
def vcZkBooReps : Nat := ZkSoundnessProfile.quantum128.repetitions

/-- Legacy classical-ROM repetition count (`219`, `ZkSoundnessProfile::Classical128`). -/
def vcClassicalZkBooReps : Nat := ZkSoundnessProfile.classical128.repetitions

set_option exponentiation.threshold 1024 in
/-- Parameter arithmetic for 219 and 438 repetitions. These inequalities
alone are neither a ROM nor a QROM adversary theorem: they contain no oracle
query budget, commitment failure term, or adaptive Fiat–Shamir simulation. -/
theorem zkSoundnessProfile_rom_vs_qrom_bounds :
    ZkSoundnessProfile.classical128.repetitions = 219 ∧
    ZkSoundnessProfile.quantum128.repetitions = 438 ∧
    vcZkBooReps = 438 ∧
    ratLe (2 ^ ZkSoundnessProfile.classical128.repetitions, 3 ^ ZkSoundnessProfile.classical128.repetitions)
      (1, 2 ^ 128) ∧
    ratLe (1, 2 ^ 130)
      (2 ^ ZkSoundnessProfile.classical128.repetitions, 3 ^ ZkSoundnessProfile.classical128.repetitions) ∧
    ratLe (2 ^ ZkSoundnessProfile.quantum128.repetitions, 3 ^ ZkSoundnessProfile.quantum128.repetitions)
      (1, 2 ^ 256) := by
  unfold ZkSoundnessProfile.repetitions vcZkBooReps ratLe
  decide

/-- 6-limb Goldilocks digest (`[u64; 6]`, `VC_DIGEST_LIMBS = 6`, `blind_vc.rs:41`):
    6-limb rate/capacity (`p^6 > 2^{383}`), providing `> 191`-bit classical birthday and
    `≥ 128`-bit (`p^2 > 2^{127.9999999996}`) post-quantum BHT / CNS sponge security. -/
structure Lane6 where
  x0 : Goldilocks
  x1 : Goldilocks
  x2 : Goldilocks
  x3 : Goldilocks
  x4 : Goldilocks
  x5 : Goldilocks
  deriving DecidableEq, Repr

theorem Lane6.ext {a b : Lane6}
    (h0 : a.x0 = b.x0) (h1 : a.x1 = b.x1) (h2 : a.x2 = b.x2)
    (h3 : a.x3 = b.x3) (h4 : a.x4 = b.x4) (h5 : a.x5 = b.x5) : a = b := by
  cases a; cases b; subst h0 h1 h2 h3 h4 h5; rfl

def lane6Zero : Lane6 :=
  ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
   Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩

def lane6Add (a b : Lane6) : Lane6 :=
  ⟨Goldilocks.add a.x0 b.x0, Goldilocks.add a.x1 b.x1, Goldilocks.add a.x2 b.x2,
   Goldilocks.add a.x3 b.x3, Goldilocks.add a.x4 b.x4, Goldilocks.add a.x5 b.x5⟩

def lane6Sub (a b : Lane6) : Lane6 :=
  ⟨Goldilocks.sub a.x0 b.x0, Goldilocks.sub a.x1 b.x1, Goldilocks.sub a.x2 b.x2,
   Goldilocks.sub a.x3 b.x3, Goldilocks.sub a.x4 b.x4, Goldilocks.sub a.x5 b.x5⟩

def lane6Scale (c : Goldilocks) (a : Lane6) : Lane6 :=
  ⟨Goldilocks.mul c a.x0, Goldilocks.mul c a.x1, Goldilocks.mul c a.x2,
   Goldilocks.mul c a.x3, Goldilocks.mul c a.x4, Goldilocks.mul c a.x5⟩

def state12Rate6 (st : Poseidon2State12) : Lane6 :=
  ⟨st.b0.x0, st.b0.x1, st.b0.x2, st.b0.x3, st.b1.x0, st.b1.x1⟩

def state12Cap6 (st : Poseidon2State12) : Lane6 :=
  ⟨st.b1.x2, st.b1.x3, st.b2.x0, st.b2.x1, st.b2.x2, st.b2.x3⟩

def mkState12Of6 (rate cap : Lane6) : Poseidon2State12 :=
  ⟨⟨rate.x0, rate.x1, rate.x2, rate.x3⟩,
   ⟨rate.x4, rate.x5, cap.x0, cap.x1⟩,
   ⟨cap.x2, cap.x3, cap.x4, cap.x5⟩⟩

private theorem state12Rate6_mk (r c : Lane6) : state12Rate6 (mkState12Of6 r c) = r := rfl
private theorem state12Cap6_mk (r c : Lane6) : state12Cap6 (mkState12Of6 r c) = c := rfl

private theorem mkState12Of6_eta (st : Poseidon2State12) :
    mkState12Of6 (state12Rate6 st) (state12Cap6 st) = st := by
  rcases st with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩
  rfl

/-- Domain tag `"VCATTRV1"` (`0x5643_4154_5452_5631`, `blind_vc.rs:53`). -/
def vcAttrCommitTag : UInt64 := 0x5643415454525631

/-- Domain tag `"VCPRESV1"` (`0x5643_5052_4553_5631`, `blind_vc.rs:54`). -/
def vcPresCommitTag : UInt64 := 0x5643505245535631

/-- Domain tag `"VCSCOPV1"` (`0x5643_5343_4F50_5631`, `blind_vc.rs:55`). -/
def vcScopeTagDom : UInt64 := 0x564353434F505631

/-- Domain tag `"VCMKLEV1"` (`0x5643_4D4B_4C45_5631`, `blind_vc.rs:56`). -/
def vcMerkleNodeTag : UInt64 := 0x56434D4B4C455631

/-- Exact 3-permutation Width-12 (`rate = 6, capacity = 6`) `Poseidon2` sponge (`blind_vc.rs:98-115`):
    absorbs three 6-limb rate chunks `(c0, c1, c2)` with capacity `lane6Zero` and outputs the
    permuted 12-limb state (whose 6-limb rate `state12Rate6` is the 6-limb digest). -/
@[expose] def absorbRate6Sponge3 (c0 c1 c2 : Lane6) : Poseidon2State12 :=
  let p1 := poseidon2Perm12 (mkState12Of6 c0 lane6Zero)
  let p2 := poseidon2Perm12 (mkState12Of6 (lane6Add (state12Rate6 p1) c1) (state12Cap6 p1))
  poseidon2Perm12 (mkState12Of6 (lane6Add (state12Rate6 p2) c2) (state12Cap6 p2))

private theorem gold_add_left_cancel_vc {a b c : Goldilocks}
    (h : Goldilocks.add a b = Goldilocks.add a c) : b = c := by
  have hs := congrArg (fun z => Goldilocks.sub z a) h
  have hCancel : ∀ x y : Goldilocks, Goldilocks.sub (Goldilocks.add x y) x = y := fun x y => by
    rw [← goldOfInt_nat x, ← goldOfInt_nat y]
    simp only [goldOfInt_add, goldOfInt_sub]
    congr 1; omega
  rwa [hCancel, hCancel] at hs

private theorem gold_add_right_cancel_vc {a b c : Goldilocks}
    (h : Goldilocks.add a c = Goldilocks.add b c) : a = b := by
  have hs := congrArg (fun z => Goldilocks.sub z c) h
  have hCancel : ∀ x y : Goldilocks, Goldilocks.sub (Goldilocks.add x y) y = x := fun x y => by
    rw [← goldOfInt_nat x, ← goldOfInt_nat y]
    simp only [goldOfInt_add, goldOfInt_sub]
    congr 1; omega
  rwa [hCancel, hCancel] at hs

private theorem lane6Add_left_cancel {a b c : Lane6}
    (h : lane6Add a b = lane6Add a c) : b = c :=
  Lane6.ext
    (gold_add_left_cancel_vc (congrArg Lane6.x0 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x1 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x2 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x3 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x4 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x5 h))

/-- Equal output halves of a public permutation. This unrestricted relation
is not a hardness assumption; use `blindVcReachableBinding204` to retain sponge reachability. -/
def Poseidon2Perm12Sponge6Collision (stA stB : Poseidon2State12) : Prop :=
  stA ≠ stB ∧
  (state12Rate6 (poseidon2Perm12 stA) = state12Rate6 (poseidon2Perm12 stB) ∨
   state12Cap6 (poseidon2Perm12 stA) = state12Cap6 (poseidon2Perm12 stB))

/-- Constructive sponge collision reduction (`0 Classical.choice`):
    any two distinct 3-chunk sequences `(c0₁, c1₁, c2₁) ≠ (c0₂, c1₂, c2₂)` colliding on
    `state12Rate6 (absorbRate6Sponge3 ...)` exhibit an explicit `Poseidon2Perm12Sponge6Collision`. -/
theorem absorbRate6Sponge3_collision_reduction
    {c0₁ c1₁ c2₁ c0₂ c1₂ c2₂ : Lane6}
    (hNe : (c0₁, c1₁, c2₁) ≠ (c0₂, c1₂, c2₂))
    (hDig : state12Rate6 (absorbRate6Sponge3 c0₁ c1₁ c2₁) =
            state12Rate6 (absorbRate6Sponge3 c0₂ c1₂ c2₂)) :
    ∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB := by
  let s1₁ := mkState12Of6 c0₁ lane6Zero
  let s1₂ := mkState12Of6 c0₂ lane6Zero
  let p1₁ := poseidon2Perm12 s1₁
  let p1₂ := poseidon2Perm12 s1₂
  let s2₁ := mkState12Of6 (lane6Add (state12Rate6 p1₁) c1₁) (state12Cap6 p1₁)
  let s2₂ := mkState12Of6 (lane6Add (state12Rate6 p1₂) c1₂) (state12Cap6 p1₂)
  let p2₁ := poseidon2Perm12 s2₁
  let p2₂ := poseidon2Perm12 s2₂
  let s3₁ := mkState12Of6 (lane6Add (state12Rate6 p2₁) c2₁) (state12Cap6 p2₁)
  let s3₂ := mkState12Of6 (lane6Add (state12Rate6 p2₂) c2₂) (state12Cap6 p2₂)
  if h3 : s3₁ = s3₂ then
    if h2 : s2₁ = s2₂ then
      have hp2 : p2₁ = p2₂ := congrArg poseidon2Perm12 h2
      have hRate3 : lane6Add (state12Rate6 p2₁) c2₁ = lane6Add (state12Rate6 p2₂) c2₂ := by
        have hr := congrArg state12Rate6 h3
        rwa [state12Rate6_mk, state12Rate6_mk] at hr
      rw [hp2] at hRate3
      have hc2 : c2₁ = c2₂ := lane6Add_left_cancel hRate3
      if h1 : s1₁ = s1₂ then
        have hp1 : p1₁ = p1₂ := congrArg poseidon2Perm12 h1
        have hRate2 : lane6Add (state12Rate6 p1₁) c1₁ = lane6Add (state12Rate6 p1₂) c1₂ := by
          have hr := congrArg state12Rate6 h2
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        rw [hp1] at hRate2
        have hc1 : c1₁ = c1₂ := lane6Add_left_cancel hRate2
        have hc0 : c0₁ = c0₂ := by
          have hr := congrArg state12Rate6 h1
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        exact False.elim (hNe (by rw [hc0, hc1, hc2]))
      else
        have hCap1 : state12Cap6 p1₁ = state12Cap6 p1₂ := by
          have hc := congrArg state12Cap6 h2
          rwa [state12Cap6_mk, state12Cap6_mk] at hc
        exact ⟨s1₁, s1₂, h1, Or.inr hCap1⟩
    else
      have hCap2 : state12Cap6 p2₁ = state12Cap6 p2₂ := by
        have hc := congrArg state12Cap6 h3
        rwa [state12Cap6_mk, state12Cap6_mk] at hc
      exact ⟨s2₁, s2₂, h2, Or.inr hCap2⟩
  else
    exact ⟨s3₁, s3₂, h3, Or.inl hDig⟩

/-- Fixed-arity credential schema (`1 ≤ arity ≤ 6`, matching `VcSchema::new` in `blind_vc.rs:79-85`). -/
structure VcSchema where
  schemaId : UInt64
  arity : Nat
  hArityPos : 1 ≤ arity
  hArityLe : arity ≤ vcMaxAttrs
  deriving DecidableEq, Repr

theorem VcSchema.ext {s₁ s₂ : VcSchema}
    (hId : s₁.schemaId = s₂.schemaId) (hAr : s₁.arity = s₂.arity) : s₁ = s₂ := by
  cases s₁; cases s₂; dsimp only at hId hAr; subst hId hAr; rfl

/-- Low 32-bit limb `schema_id & 0xffff_ffff` (`blind_vc.rs:129, 155, 181`). -/
def vcSchemaLo (sid : UInt64) : Goldilocks :=
  Goldilocks.ofNat (sid.toNat % 4294967296)

/-- High 32-bit limb combined with reduced 64-bit domain tag (`blind_vc.rs:130, 156, 184`). -/
def vcSchemaHiWithTag (sid tag : UInt64) : Goldilocks :=
  Goldilocks.add (Goldilocks.ofNat (sid.toNat / 4294967296)) (Goldilocks.ofNat tag.toNat)

/-- Zero-extended slot lookup `attrs[idx]` (`blind_vc.rs:839-845`). -/
def vcAttrAt (attrs : List Goldilocks) (idx : Nat) : Goldilocks :=
  (attrs[idx]?).getD Goldilocks.zero

/-- 13-limb + `1` separator rate-6 chunking for `compute_vc_poseidon2_commit` (`blind_vc.rs:118-137`):
    explicitly absorbs `Goldilocks.ofNat schema.arity` in `c2.x0` followed by separator `1` in `c2.x1`! -/
def vcCommitChunks (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) :
    Lane6 × Lane6 × Lane6 :=
  (⟨vcAttrAt attrs 0, vcAttrAt attrs 1, vcAttrAt attrs 2,
    vcAttrAt attrs 3, vcAttrAt attrs 4, vcAttrAt attrs 5⟩,
   ⟨blind.x0, blind.x1, blind.x2, blind.x3,
    vcSchemaLo schema.schemaId, vcSchemaHiWithTag schema.schemaId tag⟩,
   ⟨Goldilocks.ofNat schema.arity, Goldilocks.one,
    Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)

/-- Arity-framed 6-limb `BlindVC` commitment (`blind_vc.rs:112-138`, fixing `C0-3`):
    enforces `attrs.length = schema.arity` (`1 ≤ arity ≤ 6`), absorbs `schema.arity` into the
    3-permutation rate-6/capacity-6 sponge, and squeezes the 6-limb (`> 383`-bit) digest `Lane6`. -/
@[expose] def computeVcPoseidon2Commit
    (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) : Option Lane6 :=
  if attrs.length = schema.arity then
    let (c0, c1, c2) := vcCommitChunks schema attrs blind tag
    some (state12Rate6 (absorbRate6Sponge3 c0 c1 c2))
  else
    none

private theorem vcSchema_limbs_injective {sid₁ sid₂ tag : UInt64}
    (hLo : vcSchemaLo sid₁ = vcSchemaLo sid₂)
    (hHi : vcSchemaHiWithTag sid₁ tag = vcSchemaHiWithTag sid₂ tag) :
    sid₁ = sid₂ := by
  have hx := sid₁.toNat_lt_size
  have hy := sid₂.toNat_lt_size
  have hp : 4294967296 < goldilocksPrime := by decide
  have hPos : 0 < 4294967296 := by decide
  have hxl : sid₁.toNat % 4294967296 < goldilocksPrime :=
    Nat.lt_trans (Nat.mod_lt sid₁.toNat hPos) hp
  have hyl : sid₂.toNat % 4294967296 < goldilocksPrime :=
    Nat.lt_trans (Nat.mod_lt sid₂.toNat hPos) hp
  have hdiv1 : sid₁.toNat / 4294967296 < 4294967296 := by
    change sid₁.toNat < 18446744073709551616 at hx
    omega
  have hdiv2 : sid₂.toNat / 4294967296 < 4294967296 := by
    change sid₂.toNat < 18446744073709551616 at hy
    omega
  have hxh : sid₁.toNat / 4294967296 < goldilocksPrime := Nat.lt_trans hdiv1 hp
  have hyh : sid₂.toNat / 4294967296 < goldilocksPrime := Nat.lt_trans hdiv2 hp
  have hLoVal := congrArg Goldilocks.val hLo
  simp only [vcSchemaLo, Goldilocks.ofNat_val, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] at hLoVal
  have hHiSub := gold_add_right_cancel_vc hHi
  have hHiVal := congrArg Goldilocks.val hHiSub
  simp only [Goldilocks.ofNat_val, Nat.mod_eq_of_lt hxh, Nat.mod_eq_of_lt hyh] at hHiVal
  apply UInt64.toNat_inj.mp
  omega

private theorem vcCommitChunks_injective
    {schema₁ schema₂ : VcSchema} {attrs₁ attrs₂ : List Goldilocks}
    {blind₁ blind₂ : Lane4} {tag : UInt64}
    (hLen₁ : attrs₁.length = schema₁.arity)
    (hLen₂ : attrs₂.length = schema₂.arity)
    (hEq : vcCommitChunks schema₁ attrs₁ blind₁ tag = vcCommitChunks schema₂ attrs₂ blind₂ tag) :
    schema₁ = schema₂ ∧ attrs₁ = attrs₂ ∧ blind₁ = blind₂ := by
  have hArVal := congrArg (fun p => p.2.2.x0.val) hEq
  dsimp only [vcCommitChunks] at hArVal
  have hp6 : 6 < goldilocksPrime := by decide
  have hArLt₁ : schema₁.arity < goldilocksPrime := by
    have hLe := schema₁.hArityLe
    unfold vcMaxAttrs at hLe
    omega
  have hArLt₂ : schema₂.arity < goldilocksPrime := by
    have hLe := schema₂.hArityLe
    unfold vcMaxAttrs at hLe
    omega
  simp only [Goldilocks.ofNat_val, Nat.mod_eq_of_lt hArLt₁, Nat.mod_eq_of_lt hArLt₂] at hArVal
  have hSid : schema₁.schemaId = schema₂.schemaId :=
    vcSchema_limbs_injective
      (congrArg (fun p => p.2.1.x4) hEq)
      (congrArg (fun p => p.2.1.x5) hEq)
  have hSchema : schema₁ = schema₂ := VcSchema.ext hSid hArVal
  have hBlind : blind₁ = blind₂ :=
    Lane4.ext
      (congrArg (fun p => p.2.1.x0) hEq)
      (congrArg (fun p => p.2.1.x1) hEq)
      (congrArg (fun p => p.2.1.x2) hEq)
      (congrArg (fun p => p.2.1.x3) hEq)
  have h0 : vcAttrAt attrs₁ 0 = vcAttrAt attrs₂ 0 := congrArg (fun p => p.1.x0) hEq
  have h1 : vcAttrAt attrs₁ 1 = vcAttrAt attrs₂ 1 := congrArg (fun p => p.1.x1) hEq
  have h2 : vcAttrAt attrs₁ 2 = vcAttrAt attrs₂ 2 := congrArg (fun p => p.1.x2) hEq
  have h3 : vcAttrAt attrs₁ 3 = vcAttrAt attrs₂ 3 := congrArg (fun p => p.1.x3) hEq
  have h4 : vcAttrAt attrs₁ 4 = vcAttrAt attrs₂ 4 := congrArg (fun p => p.1.x4) hEq
  have h5 : vcAttrAt attrs₁ 5 = vcAttrAt attrs₂ 5 := congrArg (fun p => p.1.x5) hEq
  have hLenEq : attrs₁.length = attrs₂.length := by omega
  have hAttrs : attrs₁ = attrs₂ := by
    apply List.ext_getElem hLenEq
    intro i hi1 hi2
    have hLe1 : attrs₁.length ≤ 6 := hLen₁ ▸ schema₁.hArityLe
    have hiMax : i < 6 := by omega
    have hGet1 : vcAttrAt attrs₁ i = attrs₁[i] := by
      unfold vcAttrAt; rw [List.getElem?_eq_getElem hi1]; rfl
    have hGet2 : vcAttrAt attrs₂ i = attrs₂[i] := by
      unfold vcAttrAt; rw [List.getElem?_eq_getElem hi2]; rfl
    rw [← hGet1, ← hGet2]
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  exact ⟨hSchema, hAttrs, hBlind⟩

set_option exponentiation.threshold 1024 in
/-- **Flagship §4.1 Theorem — `BlindVC` 6-Limb Arity-Framed Sponge Commitment Binding
    (`blind_vc_commit_binding_reduces_to_sponge12_collision`, fixing `C0-3`)**:
    1. **Explicit Arity Framing**: `computeVcPoseidon2Commit` accepts iff `1 ≤ attrs.length = schema.arity ≤ 6`;
    2. **Same-Arity & Cross-Arity Binding Reduction**: ANY two distinct openings
       `(schema₁, attrs₁, blind₁) ≠ (schema₂, attrs₂, blind₂)` (including cross-arity `[x]` vs `[x, 0]`)
       yielding `some c` constructively exhibit `Poseidon2Perm12Sponge6Collision stA stB`;
    3. **Cross-Domain Non-Confusion**: `vcAttrCommitTag` and `vcPresCommitTag` chunk tuples are disjoint;
    4. **Full 384-Bit Digest Space**: `2 ^ 383 < goldilocksPrime ^ 6`. -/
theorem blind_vc_commit_binding_reduces_to_sponge12_collision :
    (∀ (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) (c : Lane6),
      computeVcPoseidon2Commit schema attrs blind tag = some c →
      1 ≤ attrs.length ∧ attrs.length = schema.arity ∧ attrs.length ≤ vcMaxAttrs) ∧
    (∀ (schema₁ schema₂ : VcSchema) (attrs₁ attrs₂ : List Goldilocks)
       (blind₁ blind₂ : Lane4) (tag : UInt64) (c : Lane6),
      computeVcPoseidon2Commit schema₁ attrs₁ blind₁ tag = some c →
      computeVcPoseidon2Commit schema₂ attrs₂ blind₂ tag = some c →
      (schema₁, attrs₁, blind₁) ≠ (schema₂, attrs₂, blind₂) →
      ∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB) ∧
    (∀ (s₁ s₂ : VcSchema) (attrs₁ attrs₂ : List Goldilocks) (blind₁ blind₂ : Lane4),
      s₁.schemaId = s₂.schemaId →
      vcCommitChunks s₁ attrs₁ blind₁ vcAttrCommitTag ≠
        vcCommitChunks s₂ attrs₂ blind₂ vcPresCommitTag) ∧
    2 ^ 383 < goldilocksPrime ^ 6 := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro schema attrs blind tag c hCom
    unfold computeVcPoseidon2Commit at hCom
    if hLen : attrs.length = schema.arity then
      exact ⟨hLen ▸ schema.hArityPos, hLen, hLen ▸ schema.hArityLe⟩
    else
      rw [ite_false_of hLen] at hCom; cases hCom
  · intro schema₁ schema₂ attrs₁ attrs₂ blind₁ blind₂ tag c hCom1 hCom2 hNe
    unfold computeVcPoseidon2Commit at hCom1 hCom2
    if hLen1 : attrs₁.length = schema₁.arity then
      rw [ite_true_of hLen1] at hCom1
      if hLen2 : attrs₂.length = schema₂.arity then
        rw [ite_true_of hLen2] at hCom2
        injection hCom1 with hc1
        injection hCom2 with hc2
        have hChunksNe : vcCommitChunks schema₁ attrs₁ blind₁ tag ≠ vcCommitChunks schema₂ attrs₂ blind₂ tag := by
          intro hEq
          obtain ⟨hs, ha, hb⟩ := vcCommitChunks_injective hLen1 hLen2 hEq
          exact hNe (by rw [hs, ha, hb])
        exact absorbRate6Sponge3_collision_reduction hChunksNe (hc1.trans hc2.symm)
      else
        rw [ite_false_of hLen2] at hCom2; cases hCom2
    else
      rw [ite_false_of hLen1] at hCom1; cases hCom1
  · intro s₁ s₂ attrs₁ attrs₂ blind₁ blind₂ hSid hEq
    have hHi := congrArg (fun p => p.2.1.x5) hEq
    dsimp only [vcCommitChunks] at hHi
    rw [hSid] at hHi
    have hTagEq := gold_add_left_cancel_vc hHi
    have hValEq := congrArg Goldilocks.val hTagEq
    have hNeVal : (Goldilocks.ofNat vcAttrCommitTag.toNat).val ≠
        (Goldilocks.ofNat vcPresCommitTag.toNat).val := by
      unfold vcAttrCommitTag vcPresCommitTag
      simp only [Goldilocks.ofNat_val]
      decide
    exact hNeVal hValEq

/-- **`#tooth` (`tooth_unframed_trailing_zero_collision`, `C0-3`)**:
    Omitting `schema.arity` from chunk `c2` makes `(arity = 1, [x])` and `(arity = 2, [x, 0])`
    absorb **identical** sponge blocks (`rfl` — zero permutation collision needed!), whereas
    `vcCommitChunks` strictly separates `(s₁, [x])` from `(s₂, [x, 0])` and `computeVcPoseidon2Commit`
    deterministically rejects wrong-arity `[x, 0]` (`= none`)! -/
theorem tooth_unframed_trailing_zero_collision (sid : UInt64) (x : Goldilocks) (blind : Lane4) (tag : UInt64) :
    let s₁ : VcSchema := ⟨sid, 1, by decide, by decide⟩
    let s₂ : VcSchema := ⟨sid, 2, by decide, by decide⟩
    let unframedChunks (attrs : List Goldilocks) : Lane6 × Lane6 × Lane6 :=
      (⟨vcAttrAt attrs 0, vcAttrAt attrs 1, vcAttrAt attrs 2,
        vcAttrAt attrs 3, vcAttrAt attrs 4, vcAttrAt attrs 5⟩,
       ⟨blind.x0, blind.x1, blind.x2, blind.x3, vcSchemaLo sid, vcSchemaHiWithTag sid tag⟩,
       ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)
    [x] ≠ [x, Goldilocks.zero] ∧
    unframedChunks [x] = unframedChunks [x, Goldilocks.zero] ∧
    vcCommitChunks s₁ [x] blind tag ≠ vcCommitChunks s₂ [x, Goldilocks.zero] blind tag ∧
    computeVcPoseidon2Commit s₁ [x, Goldilocks.zero] blind tag = none := by
  refine ⟨(by intro h; injection h with _ hNil; cases hNil), rfl, ?_, rfl⟩
  intro hEq
  obtain ⟨hS, _, _⟩ := vcCommitChunks_injective rfl rfl hEq
  have hAr := congrArg VcSchema.arity hS
  cases hAr

/-! ### §4.2 6-Limb Scope Tag, Merkle Accumulator & Algebraic Boolean Gate Soundness -/

/-- 12-limb + `1` separator rate-6 chunks for `compute_vc_scope_tag` (`blind_vc.rs:145-169`). -/
def vcScopeChunks (sid : UInt64) (holderBlind scopeLimbs : Lane4) : Lane6 × Lane6 × Lane6 :=
  (⟨holderBlind.x0, holderBlind.x1, holderBlind.x2, holderBlind.x3, scopeLimbs.x0, scopeLimbs.x1⟩,
   ⟨scopeLimbs.x2, scopeLimbs.x3, Goldilocks.zero, Goldilocks.zero,
    vcSchemaLo sid, vcSchemaHiWithTag sid vcScopeTagDom⟩,
   ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero,
    Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)

/-- 6-limb scope-bound pseudonym/nullifier `compute_vc_scope_tag` (`blind_vc.rs:145-170`). -/
def computeVcScopeTag (sid : UInt64) (holderBlind scopeLimbs : Lane4) : Lane6 :=
  let (c0, c1, c2) := vcScopeChunks sid holderBlind scopeLimbs
  state12Rate6 (absorbRate6Sponge3 c0 c1 c2)

/-- 16-limb + `1` separator rate-6 chunks for `merkle_hash_pair` (`blind_vc.rs:175-199`). -/
def vcMerkleChunks (left right : Lane6) (epoch : UInt64) (layer : Nat) : Lane6 × Lane6 × Lane6 :=
  (left,
   right,
   ⟨vcSchemaLo epoch, Goldilocks.ofNat layer,
    Goldilocks.ofNat vcMerkleNodeTag.toNat, vcSchemaHiWithTag epoch poseidon2ConstIV,
    Goldilocks.one, Goldilocks.zero⟩)

/-- Domain-separated 6-limb Merkle parent hash `merkle_hash_pair` (`blind_vc.rs:175-200`). -/
def vcMerkleHashPair (left right : Lane6) (epoch : UInt64) (layer : Nat) : Lane6 :=
  let (c0, c1, c2) := vcMerkleChunks left right epoch layer
  state12Rate6 (absorbRate6Sponge3 c0 c1 c2)

/-- Arithmetic 6-limb Merkle branch selector (`blind_vc.rs:2000-2035`):
    `delta = b * (sib - cur)`, `left = cur + delta`, `right = sib - delta`. -/
def vcMerkleStepArith (epoch : UInt64) (layer : Nat) (cur sib : Lane6) (b : Goldilocks) : Lane6 :=
  let delta := lane6Scale b (lane6Sub sib cur)
  let left := lane6Add cur delta
  let right := lane6Sub sib delta
  vcMerkleHashPair left right epoch layer

def evalVcMerklePathFrom (epoch : UInt64) : Nat → Lane6 → List (Goldilocks × Lane6) → Lane6
  | _, cur, [] => cur
  | layer, cur, (b, sib) :: rest =>
    evalVcMerklePathFrom epoch (layer + 1) (vcMerkleStepArith epoch layer cur sib b) rest

/-- Boolean 6-limb Merkle path specification (`false` => `cur` is left child, `true` => `cur` is right child). -/
def evalVcMerklePathBool (epoch : UInt64) : Nat → Lane6 → List (Bool × Lane6) → Lane6
  | _, cur, [] => cur
  | layer, cur, (false, sib) :: rest =>
    evalVcMerklePathBool epoch (layer + 1) (vcMerkleHashPair cur sib epoch layer) rest
  | layer, cur, (true, sib) :: rest =>
    evalVcMerklePathBool epoch (layer + 1) (vcMerkleHashPair sib cur epoch layer) rest

/-- Over prime field `Goldilocks`, `b * (1 - b) = 0` holds iff `b = 0 ∨ b = 1` (`blind_vc.rs:1994-1996`). -/
theorem goldilocks_bool_gate_zero_or_one (b : Goldilocks)
    (hZero : Goldilocks.mul b (Goldilocks.sub Goldilocks.one b) = Goldilocks.zero) :
    b = Goldilocks.zero ∨ b = Goldilocks.one := by
  have hVal := congrArg Goldilocks.val hZero
  rw [Goldilocks.mul_val, Goldilocks.zero_val] at hVal
  have hDvd : goldilocksPrime ∣ b.val * (Goldilocks.sub Goldilocks.one b).val :=
    Nat.dvd_of_mod_eq_zero hVal
  if hb0 : b.val = 0 then
    exact Or.inl (Goldilocks.ext hb0)
  else
    right
    have hbLt := b.isLt
    have hNotDvdB : ¬ (goldilocksPrime ∣ b.val) := by
      intro hd
      have hle := Nat.le_of_dvd (by omega) hd
      omega
    have hDvdSub : goldilocksPrime ∣ (Goldilocks.sub Goldilocks.one b).val :=
      (goldilocksPrime_isPrime ()).dvd_mul hDvd hNotDvdB
    have hSubLt := (Goldilocks.sub Goldilocks.one b).isLt
    have hSubVal0 : (Goldilocks.sub Goldilocks.one b).val = 0 := by
      if hs0 : (Goldilocks.sub Goldilocks.one b).val = 0 then exact hs0
      else
        have hle := Nat.le_of_dvd (by omega) hDvdSub
        omega
    have hSubEq0 : Goldilocks.sub Goldilocks.one b = Goldilocks.zero := Goldilocks.ext hSubVal0
    have hAdd := congrArg (fun z => Goldilocks.add z b) hSubEq0
    have hLhs : Goldilocks.add (Goldilocks.sub Goldilocks.one b) b = Goldilocks.one := by
      rw [← goldOfInt_nat Goldilocks.one, ← goldOfInt_nat b]
      simp only [goldOfInt_sub, goldOfInt_add]; congr 1; omega
    have hRhs : Goldilocks.add Goldilocks.zero b = b := by
      rw [← goldOfInt_nat Goldilocks.zero, ← goldOfInt_nat b]
      simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1; omega
    rw [hLhs, hRhs] at hAdd
    exact hAdd.symm

private theorem vcMerkleStepArith_zero (epoch : UInt64) (layer : Nat) (cur sib : Lane6) :
    vcMerkleStepArith epoch layer cur sib Goldilocks.zero = vcMerkleHashPair cur sib epoch layer := by
  unfold vcMerkleStepArith lane6Scale lane6Sub lane6Add
  dsimp only
  have hL : ∀ c s : Goldilocks, Goldilocks.add c (Goldilocks.mul Goldilocks.zero (Goldilocks.sub s c)) = c := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.zero]
    simp only [Goldilocks.zero_val, goldOfInt_sub, goldOfInt_mul, goldOfInt_add]
    congr 1; simp
  have hR : ∀ c s : Goldilocks, Goldilocks.sub s (Goldilocks.mul Goldilocks.zero (Goldilocks.sub s c)) = s := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.zero]
    simp only [Goldilocks.zero_val, goldOfInt_sub, goldOfInt_mul]
    congr 1; simp
  simp only [hL, hR]

private theorem vcMerkleStepArith_one (epoch : UInt64) (layer : Nat) (cur sib : Lane6) :
    vcMerkleStepArith epoch layer cur sib Goldilocks.one = vcMerkleHashPair sib cur epoch layer := by
  unfold vcMerkleStepArith lane6Scale lane6Sub lane6Add
  dsimp only
  have hL : ∀ c s : Goldilocks, Goldilocks.add c (Goldilocks.mul Goldilocks.one (Goldilocks.sub s c)) = s := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.one]
    simp only [Goldilocks.one_val, goldOfInt_sub, goldOfInt_mul, goldOfInt_add]
    congr 1; omega
  have hR : ∀ c s : Goldilocks, Goldilocks.sub s (Goldilocks.mul Goldilocks.one (Goldilocks.sub s c)) = c := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.one]
    simp only [Goldilocks.one_val, goldOfInt_sub, goldOfInt_mul]
    congr 1; omega
  simp only [hL, hR]

theorem evalVcMerklePathFrom_eq_bool (epoch : UInt64) :
    ∀ (layer : Nat) (cur : Lane6) (steps : List (Goldilocks × Lane6)),
      (∀ p ∈ steps, p.1 = Goldilocks.zero ∨ p.1 = Goldilocks.one) →
      ∃ boolSteps : List (Bool × Lane6),
        boolSteps.length = steps.length ∧
        evalVcMerklePathFrom epoch layer cur steps =
          evalVcMerklePathBool epoch layer cur boolSteps
  | _, cur, [], _ => ⟨[], rfl, rfl⟩
  | layer, cur, (b, sib) :: rest, hAll => by
    have hb := hAll (b, sib) (.head rest)
    have hRest : ∀ p ∈ rest, p.1 = Goldilocks.zero ∨ p.1 = Goldilocks.one :=
      fun p hp => hAll p (.tail _ hp)
    rcases hb with rfl | rfl
    · obtain ⟨bs, hLen, hEq⟩ :=
        evalVcMerklePathFrom_eq_bool epoch (layer + 1) (vcMerkleHashPair cur sib epoch layer) rest hRest
      refine ⟨(false, sib) :: bs, by simp [hLen], ?_⟩
      dsimp only [evalVcMerklePathFrom, evalVcMerklePathBool]
      rw [vcMerkleStepArith_zero, hEq]
    · obtain ⟨bs, hLen, hEq⟩ :=
        evalVcMerklePathFrom_eq_bool epoch (layer + 1) (vcMerkleHashPair sib cur epoch layer) rest hRest
      refine ⟨(true, sib) :: bs, by simp [hLen], ?_⟩
      dsimp only [evalVcMerklePathFrom, evalVcMerklePathBool]
      rw [vcMerkleStepArith_one, hEq]

/-! ### §4.3 `Vec`, `SimpleEquiv` Combinators, PRG Coin Tapes & 3-Party `absorbRate6Sponge3` + 6-Limb Merkle ZKBoo Verifier -/

/-- Length-indexed constructive vector (`0` Mathlib dependencies, explicit `DecidableEq`). -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

def Vec.head {α : Type} {n : Nat} : Vec α (n + 1) → α
  | .cons x _ => x

def Vec.tail {α : Type} {n : Nat} : Vec α (n + 1) → Vec α n
  | .cons _ xs => xs

private theorem Vec.eta_cons {α : Type} {n : Nat} (v : Vec α (n + 1)) :
    Vec.cons v.head v.tail = v := by
  cases v; rfl

def Vec.toList {α : Type} : {n : Nat} → Vec α n → List α
  | 0, .nil => []
  | _ + 1, .cons x xs => x :: xs.toList

theorem Vec.toList_length {α : Type} : ∀ {n : Nat} (v : Vec α n), v.toList.length = n
  | 0, .nil => rfl
  | _ + 1, .cons _ xs => by simp [Vec.toList, Vec.toList_length xs]

theorem Vec.toList_injective {α : Type} : ∀ {n : Nat} {u v : Vec α n},
    u.toList = v.toList → u = v
  | 0, .nil, .nil, _ => rfl
  | _ + 1, .cons x xs, .cons y ys, h => by
    simp only [Vec.toList] at h
    injection h with hx hxs
    rw [hx, Vec.toList_injective hxs]

def Vec.ofList {α : Type} : (xs : List α) → Vec α xs.length
  | [] => .nil
  | x :: xs => .cons x (Vec.ofList xs)

theorem Vec.toList_ofList {α : Type} : ∀ (xs : List α), (Vec.ofList xs).toList = xs
  | [] => rfl
  | x :: xs => by simp [Vec.ofList, Vec.toList, Vec.toList_ofList xs]

def Vec.replicate {α : Type} : (n : Nat) → α → Vec α n
  | 0, _ => .nil
  | n + 1, x => .cons x (Vec.replicate n x)

private theorem Vec.cons_inj {α : Type} {n : Nat} {x y : α} {xs ys : Vec α n}
    (h : Vec.cons x xs = Vec.cons y ys) : x = y ∧ xs = ys := by
  cases h
  exact ⟨rfl, rfl⟩

def Vec.decEq {α : Type} [DecidableEq α] : {n : Nat} → (u v : Vec α n) → Decidable (u = v)
  | 0, .nil, .nil => isTrue rfl
  | _ + 1, .cons x xs, .cons y ys =>
    match _root_.decEq x y, Vec.decEq xs ys with
    | isTrue hx, isTrue hxs => isTrue (by subst hx hxs; rfl)
    | isFalse hx, _ => isFalse (fun h => hx (Vec.cons_inj h).1)
    | _, isFalse hxs => isFalse (fun h => hxs (Vec.cons_inj h).2)

instance {α : Type} [DecidableEq α] {n : Nat} : DecidableEq (Vec α n) := Vec.decEq

/-- Dependent `Vec` cons bijection (`0 Classical.choice`) for multi-round / multi-level simulation. -/
private def seDepConsToFun {α β : Type} {n : Nat}
    (eqHead : SimpleEquiv α β)
    (eqTail : α → SimpleEquiv (Vec α n) (Vec β n)) :
    Vec α (n + 1) → Vec β (n + 1)
  | .cons x xs => .cons (eqHead.toFun x) ((eqTail x).toFun xs)

private def seDepConsInvFun {α β : Type} {n : Nat}
    (eqHead : SimpleEquiv α β)
    (eqTail : α → SimpleEquiv (Vec α n) (Vec β n)) :
    Vec β (n + 1) → Vec α (n + 1)
  | .cons y ys =>
    let x := eqHead.invFun y
    .cons x ((eqTail x).invFun ys)

private def seDepCons {α β : Type} {n : Nat}
    (eqHead : SimpleEquiv α β)
    (eqTail : α → SimpleEquiv (Vec α n) (Vec β n)) :
    SimpleEquiv (Vec α (n + 1)) (Vec β (n + 1)) where
  toFun := seDepConsToFun eqHead eqTail
  invFun := seDepConsInvFun eqHead eqTail
  left_inv
    | .cons x xs => by
      simp only [seDepConsToFun, seDepConsInvFun]
      rw [eqHead.left_inv x, (eqTail x).left_inv xs]
  right_inv
    | .cons y ys => by
      simp only [seDepConsToFun, seDepConsInvFun]
      rw [eqHead.right_inv y, (eqTail (eqHead.invFun y)).right_inv ys]

private def seVecCongr {α β : Type} : {n : Nat} → (Fin n → SimpleEquiv α β) → SimpleEquiv (Vec α n) (Vec β n)
  | 0, _ =>
    { toFun := fun _ => .nil
      invFun := fun _ => .nil
      left_inv := fun | .nil => rfl
      right_inv := fun | .nil => rfl }
  | n + 1, fs =>
    seDepCons (fs ⟨0, Nat.zero_lt_succ n⟩)
      (fun _ => seVecCongr (fun i => fs ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))

abbrev VcWire3 := Fin 3 → Goldilocks
abbrev VcLane4_3 := Fin 3 → Lane4
abbrev VcLane6_3 := Fin 3 → Lane6
abbrev VcState12_3 := Fin 3 → Poseidon2State12

/-- Cyclic adjacent ZKBoo party `(e + 1) % 3` (`blind_vc.rs:334, 1916`). -/
def vcNextParty3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

/-- Unopened 3rd ZKBoo party `(e + 2) % 3` (`blind_vc.rs:766`). -/
def vcUnopenedParty3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1

/-- Assemble a 3-party assignment from values at `(e, (e+1)%3, (e+2)%3)`. -/
def mkParty3At {α : Type} (e : Fin 3) (vE vE1 vU : α) : Fin 3 → α :=
  match e with
  | ⟨0, _⟩ => fun | ⟨0, _⟩ => vE | ⟨1, _⟩ => vE1 | ⟨2, _⟩ => vU
  | ⟨1, _⟩ => fun | ⟨0, _⟩ => vU | ⟨1, _⟩ => vE  | ⟨2, _⟩ => vE1
  | ⟨2, _⟩ => fun | ⟨0, _⟩ => vE1 | ⟨1, _⟩ => vU | ⟨2, _⟩ => vE

private theorem fin3_eq_012 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨iv, hiv⟩
  have hc : iv = 0 ∨ iv = 1 ∨ iv = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem fin3_all {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  rcases fin3_eq_012 i with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

private theorem mkParty3At_e {α : Type} (e : Fin 3) (vE vE1 vU : α) :
    mkParty3At e vE vE1 vU e = vE := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

private theorem mkParty3At_next {α : Type} (e : Fin 3) (vE vE1 vU : α) :
    mkParty3At e vE vE1 vU (vcNextParty3 e) = vE1 := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

private theorem mkParty3At_unopened {α : Type} (e : Fin 3) (vE vE1 vU : α) :
    mkParty3At e vE vE1 vU (vcUnopenedParty3 e) = vU := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

private theorem mkParty3At_eta {α : Type} (e : Fin 3) (f : Fin 3 → α) :
    mkParty3At e (f e) (f (vcNextParty3 e)) (f (vcUnopenedParty3 e)) = f := by
  funext i
  rcases fin3_eq_012 e with rfl | rfl | rfl <;>
    rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl

private theorem vcNextParty3_next_eq_unopened (e : Fin 3) :
    vcNextParty3 (vcNextParty3 e) = vcUnopenedParty3 e := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

def vcSum3 (w : VcWire3) : Goldilocks :=
  Goldilocks.add (Goldilocks.add (w 0) (w 1)) (w 2)

def vcSumLane4_3 (w : VcLane4_3) : Lane4 :=
  lane4Add (lane4Add (w 0) (w 1)) (w 2)

def vcSumLane6_3 (w : VcLane6_3) : Lane6 :=
  lane6Add (lane6Add (w 0) (w 1)) (w 2)

def vcSumState12_3 (st : VcState12_3) : Poseidon2State12 :=
  state12Add (state12Add (st 0) (st 1)) (st 2)

private theorem vcSumLane4_3_eq (w : VcLane4_3) :
    vcSumLane4_3 w =
      ⟨vcSum3 (fun i => (w i).x0), vcSum3 (fun i => (w i).x1),
       vcSum3 (fun i => (w i).x2), vcSum3 (fun i => (w i).x3)⟩ := by
  unfold vcSumLane4_3 vcSum3
  simp only [lane4Add_eq]

private theorem vcSumLane6_3_eq (w : VcLane6_3) :
    vcSumLane6_3 w =
      ⟨vcSum3 (fun i => (w i).x0), vcSum3 (fun i => (w i).x1),
       vcSum3 (fun i => (w i).x2), vcSum3 (fun i => (w i).x3),
       vcSum3 (fun i => (w i).x4), vcSum3 (fun i => (w i).x5)⟩ := rfl

private theorem vcSumState12_3_lanes (st : VcState12_3) :
    vcSumState12_3 st =
      ⟨vcSumLane4_3 (fun i => (st i).b0),
       vcSumLane4_3 (fun i => (st i).b1),
       vcSumLane4_3 (fun i => (st i).b2)⟩ := by
  unfold vcSumState12_3 vcSumLane4_3
  simp only [state12Add_eq, lane4Add_eq]

private theorem vcSumState12_3_of6 (r c : VcLane6_3) :
    vcSumState12_3 (fun i => mkState12Of6 (r i) (c i)) =
      mkState12Of6 (vcSumLane6_3 r) (vcSumLane6_3 c) := by
  rw [vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, mkState12Of6, vcSumLane6_3_eq]

private theorem state12Rate6_vcSum (st : VcState12_3) :
    state12Rate6 (vcSumState12_3 st) = vcSumLane6_3 (fun i => state12Rate6 (st i)) := by
  rw [vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, state12Rate6, vcSumLane6_3_eq]

private theorem state12Cap6_vcSum (st : VcState12_3) :
    state12Cap6 (vcSumState12_3 st) = vcSumLane6_3 (fun i => state12Cap6 (st i)) := by
  rw [vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, state12Cap6, vcSumLane6_3_eq]

private theorem vcSum3_zero : vcSum3 (fun _ => Goldilocks.zero) = Goldilocks.zero := by
  unfold vcSum3
  rw [← goldOfInt_nat Goldilocks.zero]
  simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1

private theorem vcSumLane6_3_zero : vcSumLane6_3 (fun _ => lane6Zero) = lane6Zero := by
  rw [vcSumLane6_3_eq]
  simp only [lane6Zero, vcSum3_zero]

private theorem vcSum3_add (a b : VcWire3) :
    vcSum3 (fun i => Goldilocks.add (a i) (b i)) = Goldilocks.add (vcSum3 a) (vcSum3 b) := by
  unfold vcSum3
  dsimp only
  rw [← goldOfInt_nat (a 0), ← goldOfInt_nat (b 0), ← goldOfInt_nat (a 1),
      ← goldOfInt_nat (b 1), ← goldOfInt_nat (a 2), ← goldOfInt_nat (b 2)]
  simp only [goldOfInt_add]; congr 1; omega

private theorem vcSum3_sub (a b : VcWire3) :
    vcSum3 (fun i => Goldilocks.sub (a i) (b i)) = Goldilocks.sub (vcSum3 a) (vcSum3 b) := by
  unfold vcSum3
  dsimp only
  rw [← goldOfInt_nat (a 0), ← goldOfInt_nat (b 0), ← goldOfInt_nat (a 1),
      ← goldOfInt_nat (b 1), ← goldOfInt_nat (a 2), ← goldOfInt_nat (b 2)]
  simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega

private theorem vcSumLane6_3_add (a b : VcLane6_3) :
    vcSumLane6_3 (fun i => lane6Add (a i) (b i)) = lane6Add (vcSumLane6_3 a) (vcSumLane6_3 b) := by
  simp only [vcSumLane6_3_eq, lane6Add, vcSum3_add]

private theorem vcUnopened_of_sum3 (e : Fin 3) {w : VcWire3} {target : Goldilocks}
    (hSum : vcSum3 w = target) :
    w = mkParty3At e (w e) (w (vcNextParty3 e))
          (Goldilocks.sub (Goldilocks.sub target (w e)) (w (vcNextParty3 e))) := by
  rw [← hSum]
  have hUn : w (vcUnopenedParty3 e) =
      Goldilocks.sub (Goldilocks.sub (vcSum3 w) (w e)) (w (vcNextParty3 e)) := by
    unfold vcSum3
    rcases fin3_eq_012 e with rfl | rfl | rfl <;>
      (dsimp only [vcNextParty3, vcUnopenedParty3];
       rw [← goldOfInt_nat (w 0), ← goldOfInt_nat (w 1), ← goldOfInt_nat (w 2)];
       simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega)
  rw [← hUn, mkParty3At_eta]

private theorem vcUnopened_of_sumLane6_3 (e : Fin 3) {w : VcLane6_3} {target : Lane6}
    (hSum : vcSumLane6_3 w = target) :
    w = mkParty3At e (w e) (w (vcNextParty3 e))
          (lane6Sub (lane6Sub target (w e)) (w (vcNextParty3 e))) := by
  have hx0 := vcUnopened_of_sum3 e (w := fun i => (w i).x0) (congrArg Lane6.x0 hSum)
  have hx1 := vcUnopened_of_sum3 e (w := fun i => (w i).x1) (congrArg Lane6.x1 hSum)
  have hx2 := vcUnopened_of_sum3 e (w := fun i => (w i).x2) (congrArg Lane6.x2 hSum)
  have hx3 := vcUnopened_of_sum3 e (w := fun i => (w i).x3) (congrArg Lane6.x3 hSum)
  have hx4 := vcUnopened_of_sum3 e (w := fun i => (w i).x4) (congrArg Lane6.x4 hSum)
  have hx5 := vcUnopened_of_sum3 e (w := fun i => (w i).x5) (congrArg Lane6.x5 hSum)
  funext i
  apply Lane6.ext
  · have h := congrFun hx0 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx1 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx2 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx3 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx4 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx5 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h

/-- Opened 2-party wire projection `(w e, w ((e + 1) % 3))`. -/
def vcPairAt (w : VcWire3) (e : Fin 3) : Goldilocks × Goldilocks :=
  (w e, w (vcNextParty3 e))

def vcPairAtLane6 (w : VcLane6_3) (e : Fin 3) : Lane6 × Lane6 :=
  (w e, w (vcNextParty3 e))

def vcPairAtState12 (st : VcState12_3) (e : Fin 3) : Poseidon2State12 × Poseidon2State12 :=
  (st e, st (vcNextParty3 e))

/-- 2-party public constant addition `ZkBooVerifierTape::add_const` (`blind_vc.rs:352-359`). -/
def vcPairAddConst (e : Fin 3) (x : Goldilocks × Goldilocks) (c : Goldilocks) :
    Goldilocks × Goldilocks :=
  if e = 0 then (Goldilocks.add x.1 c, x.2)
  else if vcNextParty3 e = 0 then (x.1, Goldilocks.add x.2 c)
  else x

def vcWireAddConst3 (w : VcWire3) (c : Goldilocks) : VcWire3 :=
  fun i => if i = 0 then Goldilocks.add (w 0) c else w i

def vcConstWire3 (c : Goldilocks) : VcWire3 :=
  fun i => if i = 0 then c else Goldilocks.zero

def vcConstPair (e : Fin 3) (c : Goldilocks) : Goldilocks × Goldilocks :=
  vcPairAddConst e (Goldilocks.zero, Goldilocks.zero) c

private theorem vcPairAddConst_spec (w : VcWire3) (c : Goldilocks) (e : Fin 3) :
    vcPairAddConst e (vcPairAt w e) c = vcPairAt (vcWireAddConst3 w c) e := by
  rcases e with ⟨ev, hev⟩
  have hCases : ev = 0 ∨ ev = 1 ∨ ev = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> rfl

private theorem vcConstPair_spec (c : Goldilocks) (e : Fin 3) :
    vcConstPair e c = vcPairAt (vcConstWire3 c) e := by
  have hz : Goldilocks.add Goldilocks.zero c = c := by
    rw [← goldOfInt_nat Goldilocks.zero, ← goldOfInt_nat c]
    simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1; omega
  have he : e = 0 ∨ e = 1 ∨ e = 2 := by revert e; decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  rcases he with rfl | rfl | rfl
  · simp only [vcConstPair, vcPairAddConst, vcPairAt, vcConstWire3, vcNextParty3, ↓reduceIte, h10, hz]
  · simp only [vcConstPair, vcPairAddConst, vcPairAt, vcConstWire3, vcNextParty3, ↓reduceIte, h10, h20]
  · simp only [vcConstPair, vcPairAddConst, vcPairAt, vcConstWire3, vcNextParty3, ↓reduceIte, h20, hz]

private theorem vcSum3_addConst (w : VcWire3) (c : Goldilocks) :
    vcSum3 (vcWireAddConst3 w c) = Goldilocks.add (vcSum3 w) c := by
  unfold vcSum3 vcWireAddConst3
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  simp only [↓reduceIte, h1, h2]
  rw [← goldOfInt_nat (w 0), ← goldOfInt_nat (w 1), ← goldOfInt_nat (w 2), ← goldOfInt_nat c]
  simp only [goldOfInt_add]; congr 1; omega

private theorem vcSum3_constWire (c : Goldilocks) :
    vcSum3 (vcConstWire3 c) = c := by
  unfold vcSum3 vcConstWire3
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  simp only [↓reduceIte, h1, h2]
  rw [← goldOfInt_nat c, ← goldOfInt_nat Goldilocks.zero]
  simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1

/-- Structured per-party gate randomness types for `"QSAG.VC.ZKBOO_R.V1"` PRG expansion. -/
abbrev SboxCoins := Goldilocks × Goldilocks × Goldilocks × Goldilocks

structure ExtRoundCoins where
  s0 : SboxCoins
  s1 : SboxCoins
  s2 : SboxCoins
  s3 : SboxCoins
  s4 : SboxCoins
  s5 : SboxCoins
  s6 : SboxCoins
  s7 : SboxCoins
  s8 : SboxCoins
  s9 : SboxCoins
  s10 : SboxCoins
  s11 : SboxCoins
  deriving DecidableEq, Repr

structure Perm12Coins where
  initExt : Vec ExtRoundCoins poseidon2InitialExtConsts.length
  internal : Vec SboxCoins poseidon2InternalConsts.length
  termExt : Vec ExtRoundCoins poseidon2TerminalExtConsts.length
  deriving DecidableEq

structure Sponge3Coins where
  perm1 : Perm12Coins
  perm2 : Perm12Coins
  perm3 : Perm12Coins
  deriving DecidableEq

structure MerkleLevelCoins where
  boolR : Goldilocks
  sel0R : Goldilocks
  sel1R : Goldilocks
  sel2R : Goldilocks
  sel3R : Goldilocks
  sel4R : Goldilocks
  sel5R : Goldilocks
  hashCoins : Sponge3Coins
  deriving DecidableEq

structure PartyGateCoins (treeDepth : Nat) where
  attrCoins : Sponge3Coins
  presCoins : Sponge3Coins
  scopeCoins : Sponge3Coins
  merkleCoins : Vec MerkleLevelCoins treeDepth
  deriving DecidableEq

/-- Domain tag `"QSAG.VC.ZKBOO_R.V1"` (`blind_vc.rs:259`, 18 bytes) for party PRG tape expansion. -/
def vcZkBooPrgTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x56, 0x43, 0x2E, 0x5A,
   0x4B, 0x42, 0x4F, 0x4F, 0x5F, 0x52, 0x2E, 0x56, 0x31]

/-- Generic context indices are injective even beyond the u64 range. -/
theorem contextIndex204_injective {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)).1

/-- Unbounded counters in the Lean credential tape domain. -/
def vcPrgContext204 (seed : Vec UInt8 32) (rep : Nat) (party : Fin 3) (word : Nat) :
    List (List UInt8) :=
  [seed.toList, leb128 rep, [UInt8.ofNat party.val], leb128 word]

theorem vcPrgContext204_indices {seed : Vec UInt8 32} {party : Fin 3}
    {rep rep' word word' : Nat}
    (h : vcPrgContext204 seed rep party word = vcPrgContext204 seed rep' party word') :
    rep = rep' ∧ word = word' := by
  simp only [vcPrgContext204, List.cons.injEq] at h
  exact ⟨contextIndex204_injective h.2.1, contextIndex204_injective h.2.2.2.1⟩

def vcChallengeContext204 (digest : List UInt8) (rep : Nat) : List (List UInt8) :=
  [digest, leb128 rep]

theorem vcChallengeContext204_index {digest : List UInt8} {a b : Nat}
    (h : vcChallengeContext204 digest a = vcChallengeContext204 digest b) : a = b := by
  simp only [vcChallengeContext204, List.cons.injEq] at h
  exact contextIndex204_injective h.2.1

/-- Counter-mode Goldilocks PRG word stream under `"QSAG.VC.ZKBOO_R.V1"` (`blind_vc.rs:336-350`). -/
def vcPrgStreamAt (repIdx : Nat) (partyIdx : Fin 3) (tapeSeed : Vec UInt8 32) (wordIdx : Nat) : Goldilocks :=
  let blk := cshake256FramedBytes vcZkBooPrgTag
    (vcPrgContext204 tapeSeed repIdx partyIdx wordIdx)
  Goldilocks.ofNat (decodeNatLeBytes (blk.take 8))

private def sampleSboxCoins (st : Nat → Goldilocks) (pos : Nat) : SboxCoins × Nat :=
  ((st pos, st (pos + 1), st (pos + 2), st (pos + 3)), pos + 4)

private def sampleExtRoundCoins (st : Nat → Goldilocks) (pos : Nat) : ExtRoundCoins × Nat :=
  let (s0, p0) := sampleSboxCoins st pos
  let (s1, p1) := sampleSboxCoins st p0
  let (s2, p2) := sampleSboxCoins st p1
  let (s3, p3) := sampleSboxCoins st p2
  let (s4, p4) := sampleSboxCoins st p3
  let (s5, p5) := sampleSboxCoins st p4
  let (s6, p6) := sampleSboxCoins st p5
  let (s7, p7) := sampleSboxCoins st p6
  let (s8, p8) := sampleSboxCoins st p7
  let (s9, p9) := sampleSboxCoins st p8
  let (s10, p10) := sampleSboxCoins st p9
  let (s11, p11) := sampleSboxCoins st p10
  (⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩, p11)

private def sampleVecFrom {α : Type} (samp : (Nat → Goldilocks) → Nat → α × Nat)
    (st : Nat → Goldilocks) : (n : Nat) → Nat → Vec α n × Nat
  | 0, pos => (.nil, pos)
  | n + 1, pos =>
    let (h, p1) := samp st pos
    let (t, p2) := sampleVecFrom samp st n p1
    (.cons h t, p2)

private def samplePerm12Coins (st : Nat → Goldilocks) (pos : Nat) : Perm12Coins × Nat :=
  let (c1, p1) := sampleVecFrom sampleExtRoundCoins st poseidon2InitialExtConsts.length pos
  let (c2, p2) := sampleVecFrom sampleSboxCoins st poseidon2InternalConsts.length p1
  let (c3, p3) := sampleVecFrom sampleExtRoundCoins st poseidon2TerminalExtConsts.length p2
  (⟨c1, c2, c3⟩, p3)

private def sampleSponge3Coins (st : Nat → Goldilocks) (pos : Nat) : Sponge3Coins × Nat :=
  let (q1, p1) := samplePerm12Coins st pos
  let (q2, p2) := samplePerm12Coins st p1
  let (q3, p3) := samplePerm12Coins st p2
  (⟨q1, q2, q3⟩, p3)

private def sampleMerkleLevelCoins (st : Nat → Goldilocks) (pos : Nat) : MerkleLevelCoins × Nat :=
  let b := st pos
  let g0 := st (pos + 1); let g1 := st (pos + 2); let g2 := st (pos + 3)
  let g3 := st (pos + 4); let g4 := st (pos + 5); let g5 := st (pos + 6)
  let (hc, pNext) := sampleSponge3Coins st (pos + 7)
  (⟨b, g0, g1, g2, g3, g4, g5, hc⟩, pNext)

/-- Concrete `"QSAG.VC.ZKBOO_R.V1"` party PRG tape expansion (`blind_vc.rs:336-350`). -/
def vcExpandPartyCoins (treeDepth : Nat) (repIdx : Nat) (partyIdx : Fin 3) (tapeSeed : Vec UInt8 32) :
    PartyGateCoins treeDepth :=
  let st := vcPrgStreamAt repIdx partyIdx tapeSeed
  let (ac, p1) := sampleSponge3Coins st 0
  let (pc, p2) := sampleSponge3Coins st p1
  let (sc, p3) := sampleSponge3Coins st p2
  let (mc, _) := sampleVecFrom sampleMerkleLevelCoins st treeDepth p3
  ⟨ac, pc, sc, mc⟩

/-- Expected ZKBoo multiplication share `x_e * y_e + x_e * y_{e+1} + x_{e+1} * y_e + r_e - r_{e+1}`
    (`blind_vc.rs:368-373`). -/
def vcMulExpectedPair (xe xe1 ye ye1 re re1 : Goldilocks) : Goldilocks :=
  let cross := Goldilocks.add (Goldilocks.mul xe ye)
    (Goldilocks.add (Goldilocks.mul xe ye1) (Goldilocks.mul xe1 ye))
  Goldilocks.sub (Goldilocks.add cross re) re1

def vcMulGate3 (a b r : VcWire3) : VcWire3 :=
  fun i => vcMulExpectedPair (a i) (a (vcNextParty3 i)) (b i) (b (vcNextParty3 i)) (r i) (r (vcNextParty3 i))

theorem vcMulGate3_sum (a b r : VcWire3) :
    vcSum3 (vcMulGate3 a b r) = Goldilocks.mul (vcSum3 a) (vcSum3 b) := by
  unfold vcSum3 vcMulGate3 vcMulExpectedPair vcNextParty3
  dsimp only
  rw [← goldOfInt_nat (a 0), ← goldOfInt_nat (a 1), ← goldOfInt_nat (a 2),
      ← goldOfInt_nat (b 0), ← goldOfInt_nat (b 1), ← goldOfInt_nat (b 2),
      ← goldOfInt_nat (r 0), ← goldOfInt_nat (r 1), ← goldOfInt_nat (r 2)]
  simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
  congr 1
  simp only [Int.add_mul, Int.mul_add]
  omega

structure PartyMulView where
  r : Goldilocks
  out : Goldilocks
  deriving DecidableEq, Repr

def pairCheckMul (x y : Goldilocks × Goldilocks) (gE gE1 : PartyMulView) :
    Option (Goldilocks × Goldilocks) :=
  if gE.out = vcMulExpectedPair x.1 x.2 y.1 y.2 gE.r gE1.r then
    some (gE.out, gE1.out)
  else
    none

def honestMulView3 (a b r : VcWire3) : Fin 3 → PartyMulView :=
  fun i => { r := r i, out := vcMulGate3 a b r i }

private theorem pairCheckMul_step {wx wy : VcWire3} {g : Fin 3 → PartyMulView} {e : Fin 3}
    {outP : Goldilocks × Goldilocks}
    (hOk : pairCheckMul (vcPairAt wx e) (vcPairAt wy e) (g e) (g (vcNextParty3 e)) = some outP) :
    outP = vcPairAt (fun i => (g i).out) e ∧
    (g e).out = vcMulGate3 wx wy (fun i => (g i).r) e := by
  unfold pairCheckMul vcPairAt at hOk
  dsimp only at hOk
  if hEq : (g e).out = vcMulExpectedPair (wx e) (wx (vcNextParty3 e)) (wy e) (wy (vcNextParty3 e))
      (g e).r (g (vcNextParty3 e)).r then
    rw [ite_true_of hEq] at hOk
    injection hOk with hPair
    exact ⟨hPair.symm, hEq⟩
  else
    rw [ite_false_of hEq] at hOk; cases hOk

private theorem pairCheckMul_honest (wx wy r : VcWire3) (e : Fin 3) :
    pairCheckMul (vcPairAt wx e) (vcPairAt wy e)
      (honestMulView3 wx wy r e) (honestMulView3 wx wy r (vcNextParty3 e)) =
      some (vcPairAt (vcMulGate3 wx wy r) e) := by
  unfold pairCheckMul honestMulView3 vcPairAt vcMulGate3
  dsimp only
  simp only [↓reduceIte]

private theorem pairCheckMul_extract3 {wx wy : VcWire3} {g : Fin 3 → PartyMulView}
    {o0 o1 o2 : Goldilocks × Goldilocks}
    (h0 : pairCheckMul (vcPairAt wx 0) (vcPairAt wy 0) (g 0) (g 1) = some o0)
    (h1 : pairCheckMul (vcPairAt wx 1) (vcPairAt wy 1) (g 1) (g 2) = some o1)
    (h2 : pairCheckMul (vcPairAt wx 2) (vcPairAt wy 2) (g 2) (g 0) = some o2) :
    vcSum3 (fun i => (g i).out) = Goldilocks.mul (vcSum3 wx) (vcSum3 wy) := by
  have hFun : (fun i => (g i).out) = vcMulGate3 wx wy (fun i => (g i).r) :=
    funext (fin3_all (pairCheckMul_step h0).2 (pairCheckMul_step h1).2 (pairCheckMul_step h2).2)
  rw [hFun, vcMulGate3_sum]

structure PartySboxView where
  g1 : PartyMulView
  g2 : PartyMulView
  g3 : PartyMulView
  g4 : PartyMulView
  deriving DecidableEq, Repr

def extractSboxCoins (sv : PartySboxView) : SboxCoins :=
  (sv.g1.r, sv.g2.r, sv.g3.r, sv.g4.r)

def pairCheckSbox (x : Goldilocks × Goldilocks) (sE sE1 : PartySboxView) :
    Option (Goldilocks × Goldilocks) :=
  match pairCheckMul x x sE.g1 sE1.g1 with
  | none => none
  | some x2 =>
    match pairCheckMul x2 x sE.g2 sE1.g2 with
    | none => none
    | some x3 =>
      match pairCheckMul x2 x2 sE.g3 sE1.g3 with
      | none => none
      | some x4 => pairCheckMul x4 x3 sE.g4 sE1.g4

def honestSboxView3 (wx : VcWire3) (sc : Fin 3 → SboxCoins) : (Fin 3 → PartySboxView) × VcWire3 :=
  let r1 : VcWire3 := fun i => (sc i).1
  let r2 : VcWire3 := fun i => (sc i).2.1
  let r3 : VcWire3 := fun i => (sc i).2.2.1
  let r4 : VcWire3 := fun i => (sc i).2.2.2
  let g1 := honestMulView3 wx wx r1
  let w2 := vcMulGate3 wx wx r1
  let g2 := honestMulView3 w2 wx r2
  let w3 := vcMulGate3 w2 wx r2
  let g3 := honestMulView3 w2 w2 r3
  let w4 := vcMulGate3 w2 w2 r3
  let g4 := honestMulView3 w4 w3 r4
  let w7 := vcMulGate3 w4 w3 r4
  (fun i => ⟨g1 i, g2 i, g3 i, g4 i⟩, w7)

private theorem extractSboxCoins_honest (wx : VcWire3) (sc : Fin 3 → SboxCoins) (i : Fin 3) :
    extractSboxCoins ((honestSboxView3 wx sc).1 i) = sc i := rfl

private theorem honestSboxView3_sum (wx : VcWire3) (sc : Fin 3 → SboxCoins) :
    vcSum3 (honestSboxView3 wx sc).2 = sbox7 (vcSum3 wx) := by
  unfold honestSboxView3 sbox7
  dsimp only
  simp only [vcMulGate3_sum]
  have hComm : ∀ u v : Goldilocks, Goldilocks.mul u v = Goldilocks.mul v u := fun u v => by
    rw [← goldOfInt_nat u, ← goldOfInt_nat v]
    simp only [goldOfInt_mul]; congr 1; exact Int.mul_comm _ _
  exact hComm _ _

private theorem pairCheckSbox_honest (wx : VcWire3) (sc : Fin 3 → SboxCoins) (e : Fin 3) :
    pairCheckSbox (vcPairAt wx e) ((honestSboxView3 wx sc).1 e) ((honestSboxView3 wx sc).1 (vcNextParty3 e)) =
      some (vcPairAt (honestSboxView3 wx sc).2 e) := by
  unfold pairCheckSbox honestSboxView3
  dsimp only
  rw [pairCheckMul_honest]; dsimp only
  rw [pairCheckMul_honest]; dsimp only
  rw [pairCheckMul_honest]; dsimp only
  rw [pairCheckMul_honest]

private theorem pairCheckSbox_step {wx : VcWire3} {sv : Fin 3 → PartySboxView} {e : Fin 3}
    {outP : Goldilocks × Goldilocks}
    (hOk : pairCheckSbox (vcPairAt wx e) (sv e) (sv (vcNextParty3 e)) = some outP) :
    outP = vcPairAt (fun i => (sv i).g4.out) e ∧
    pairCheckMul (vcPairAt wx e) (vcPairAt wx e) (sv e).g1 (sv (vcNextParty3 e)).g1 =
      some (vcPairAt (fun i => (sv i).g1.out) e) ∧
    pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt wx e) (sv e).g2 (sv (vcNextParty3 e)).g2 =
      some (vcPairAt (fun i => (sv i).g2.out) e) ∧
    pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt (fun i => (sv i).g1.out) e)
      (sv e).g3 (sv (vcNextParty3 e)).g3 = some (vcPairAt (fun i => (sv i).g3.out) e) ∧
    pairCheckMul (vcPairAt (fun i => (sv i).g3.out) e) (vcPairAt (fun i => (sv i).g2.out) e)
      (sv e).g4 (sv (vcNextParty3 e)).g4 = some (vcPairAt (fun i => (sv i).g4.out) e) := by
  unfold pairCheckSbox at hOk
  cases hm1 : pairCheckMul (vcPairAt wx e) (vcPairAt wx e) (sv e).g1 (sv (vcNextParty3 e)).g1 with
  | none => rw [hm1] at hOk; cases hOk
  | some x2 =>
    rw [hm1] at hOk; dsimp only at hOk
    obtain ⟨hx2, _⟩ := pairCheckMul_step (g := fun i => (sv i).g1) hm1
    subst hx2
    cases hm2 : pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt wx e)
        (sv e).g2 (sv (vcNextParty3 e)).g2 with
    | none => rw [hm2] at hOk; cases hOk
    | some x3 =>
      rw [hm2] at hOk; dsimp only at hOk
      obtain ⟨hx3, _⟩ := pairCheckMul_step (g := fun i => (sv i).g2) hm2
      subst hx3
      cases hm3 : pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt (fun i => (sv i).g1.out) e)
          (sv e).g3 (sv (vcNextParty3 e)).g3 with
      | none => rw [hm3] at hOk; cases hOk
      | some x4 =>
        rw [hm3] at hOk; dsimp only at hOk
        obtain ⟨hx4, _⟩ := pairCheckMul_step (g := fun i => (sv i).g3) hm3
        subst hx4
        obtain ⟨hx7, _⟩ := pairCheckMul_step (g := fun i => (sv i).g4) hOk
        subst hx7
        exact ⟨rfl, rfl, rfl, rfl, hOk⟩

private theorem pairCheckSbox_extract3 {wx : VcWire3} {sv : Fin 3 → PartySboxView}
    {o0 o1 o2 : Goldilocks × Goldilocks}
    (h0 : pairCheckSbox (vcPairAt wx 0) (sv 0) (sv 1) = some o0)
    (h1 : pairCheckSbox (vcPairAt wx 1) (sv 1) (sv 2) = some o1)
    (h2 : pairCheckSbox (vcPairAt wx 2) (sv 2) (sv 0) = some o2) :
    vcSum3 (fun i => (sv i).g4.out) = sbox7 (vcSum3 wx) := by
  obtain ⟨_, m10, m20, m30, m40⟩ := pairCheckSbox_step h0
  obtain ⟨_, m11, m21, m31, m41⟩ := pairCheckSbox_step h1
  obtain ⟨_, m12, m22, m32, m42⟩ := pairCheckSbox_step h2
  dsimp only [vcNextParty3] at m10 m20 m30 m40 m11 m21 m31 m41 m12 m22 m32 m42
  have s1 := pairCheckMul_extract3 (g := fun i => (sv i).g1) m10 m11 m12
  have s2 := pairCheckMul_extract3 (g := fun i => (sv i).g2) m20 m21 m22
  have s3 := pairCheckMul_extract3 (g := fun i => (sv i).g3) m30 m31 m32
  have s4 := pairCheckMul_extract3 (g := fun i => (sv i).g4) m40 m41 m42
  unfold sbox7
  dsimp only
  rw [s4, s3, s2, s1]
  have hComm : ∀ u v : Goldilocks, Goldilocks.mul u v = Goldilocks.mul v u := fun u v => by
    rw [← goldOfInt_nat u, ← goldOfInt_nat v]
    simp only [goldOfInt_mul]; congr 1; exact Int.mul_comm _ _
  exact hComm _ _

structure PartyExtRoundView where
  s0 : PartySboxView
  s1 : PartySboxView
  s2 : PartySboxView
  s3 : PartySboxView
  s4 : PartySboxView
  s5 : PartySboxView
  s6 : PartySboxView
  s7 : PartySboxView
  s8 : PartySboxView
  s9 : PartySboxView
  s10 : PartySboxView
  s11 : PartySboxView
  deriving DecidableEq, Repr

def extractExtRoundCoins (rv : PartyExtRoundView) : ExtRoundCoins :=
  ⟨extractSboxCoins rv.s0, extractSboxCoins rv.s1, extractSboxCoins rv.s2, extractSboxCoins rv.s3,
   extractSboxCoins rv.s4, extractSboxCoins rv.s5, extractSboxCoins rv.s6, extractSboxCoins rv.s7,
   extractSboxCoins rv.s8, extractSboxCoins rv.s9, extractSboxCoins rv.s10, extractSboxCoins rv.s11⟩

def pairCheckExtRound (e : Fin 3) (rc : Poseidon2State12)
    (vE vE1 : PartyExtRoundView) (st : Poseidon2State12 × Poseidon2State12) :
    Option (Poseidon2State12 × Poseidon2State12) :=
  let chk (f : Poseidon2State12 → Goldilocks) (sE sE1 : PartySboxView) :=
    pairCheckSbox (vcPairAddConst e (f st.1, f st.2) (f rc)) sE sE1
  match chk (·.b0.x0) vE.s0 vE1.s0, chk (·.b0.x1) vE.s1 vE1.s1,
        chk (·.b0.x2) vE.s2 vE1.s2, chk (·.b0.x3) vE.s3 vE1.s3,
        chk (·.b1.x0) vE.s4 vE1.s4, chk (·.b1.x1) vE.s5 vE1.s5,
        chk (·.b1.x2) vE.s6 vE1.s6, chk (·.b1.x3) vE.s7 vE1.s7,
        chk (·.b2.x0) vE.s8 vE1.s8, chk (·.b2.x1) vE.s9 vE1.s9,
        chk (·.b2.x2) vE.s10 vE1.s10, chk (·.b2.x3) vE.s11 vE1.s11 with
  | some y0, some y1, some y2, some y3, some y4, some y5,
    some y6, some y7, some y8, some y9, some y10, some y11 =>
    some (applyME ⟨⟨y0.1, y1.1, y2.1, y3.1⟩, ⟨y4.1, y5.1, y6.1, y7.1⟩, ⟨y8.1, y9.1, y10.1, y11.1⟩⟩,
          applyME ⟨⟨y0.2, y1.2, y2.2, y3.2⟩, ⟨y4.2, y5.2, y6.2, y7.2⟩, ⟨y8.2, y9.2, y10.2, y11.2⟩⟩)
  | _, _, _, _, _, _, _, _, _, _, _, _ => none

def vcExtRoundOut3 (rv : Fin 3 → PartyExtRoundView) : VcState12_3 :=
  fun i =>
    applyME ⟨⟨(rv i).s0.g4.out, (rv i).s1.g4.out, (rv i).s2.g4.out, (rv i).s3.g4.out⟩,
             ⟨(rv i).s4.g4.out, (rv i).s5.g4.out, (rv i).s6.g4.out, (rv i).s7.g4.out⟩,
             ⟨(rv i).s8.g4.out, (rv i).s9.g4.out, (rv i).s10.g4.out, (rv i).s11.g4.out⟩⟩

def honestExtRound3 (rc : Poseidon2State12) (st : VcState12_3) (ec : Fin 3 → ExtRoundCoins) :
    (Fin 3 → PartyExtRoundView) × VcState12_3 :=
  let mk (f : Poseidon2State12 → Goldilocks) (sel : ExtRoundCoins → SboxCoins) :=
    honestSboxView3 (vcWireAddConst3 (fun i => f (st i)) (f rc)) (fun i => sel (ec i))
  let r0 := mk (·.b0.x0) (·.s0); let r1 := mk (·.b0.x1) (·.s1)
  let r2 := mk (·.b0.x2) (·.s2); let r3 := mk (·.b0.x3) (·.s3)
  let r4 := mk (·.b1.x0) (·.s4); let r5 := mk (·.b1.x1) (·.s5)
  let r6 := mk (·.b1.x2) (·.s6); let r7 := mk (·.b1.x3) (·.s7)
  let r8 := mk (·.b2.x0) (·.s8); let r9 := mk (·.b2.x1) (·.s9)
  let r10 := mk (·.b2.x2) (·.s10); let r11 := mk (·.b2.x3) (·.s11)
  let rv : Fin 3 → PartyExtRoundView := fun i =>
    ⟨r0.1 i, r1.1 i, r2.1 i, r3.1 i, r4.1 i, r5.1 i,
     r6.1 i, r7.1 i, r8.1 i, r9.1 i, r10.1 i, r11.1 i⟩
  (rv, vcExtRoundOut3 rv)

private theorem extractExtRoundCoins_honest (rc : Poseidon2State12) (st : VcState12_3)
    (ec : Fin 3 → ExtRoundCoins) (i : Fin 3) :
    extractExtRoundCoins ((honestExtRound3 rc st ec).1 i) = ec i := rfl

private theorem pairCheckExtRound_honest (rc : Poseidon2State12) (st : VcState12_3)
    (ec : Fin 3 → ExtRoundCoins) (e : Fin 3) :
    pairCheckExtRound e rc ((honestExtRound3 rc st ec).1 e) ((honestExtRound3 rc st ec).1 (vcNextParty3 e))
      (vcPairAtState12 st e) = some (vcPairAtState12 (honestExtRound3 rc st ec).2 e) := by
  unfold pairCheckExtRound honestExtRound3 vcPairAtState12 vcExtRoundOut3
  dsimp only
  have hAt : ∀ f : Poseidon2State12 → Goldilocks,
      vcPairAddConst e (f (st e), f (st (vcNextParty3 e))) (f rc) =
        vcPairAt (vcWireAddConst3 (fun i => f (st i)) (f rc)) e :=
    fun f => vcPairAddConst_spec (fun i => f (st i)) (f rc) e
  rw [hAt (·.b0.x0), hAt (·.b0.x1), hAt (·.b0.x2), hAt (·.b0.x3),
      hAt (·.b1.x0), hAt (·.b1.x1), hAt (·.b1.x2), hAt (·.b1.x3),
      hAt (·.b2.x0), hAt (·.b2.x1), hAt (·.b2.x2), hAt (·.b2.x3),
      pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest,
      pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest,
      pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest]
  rfl

private theorem pairCheckExtRound_step {rc : Poseidon2State12} {st : VcState12_3}
    {rv : Fin 3 → PartyExtRoundView} {e : Fin 3} {outSt : Poseidon2State12 × Poseidon2State12}
    (hOk : pairCheckExtRound e rc (rv e) (rv (vcNextParty3 e)) (vcPairAtState12 st e) = some outSt) :
    outSt = vcPairAtState12 (vcExtRoundOut3 rv) e ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc.b0.x0) e) (rv e).s0 (rv (vcNextParty3 e)).s0 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x1) rc.b0.x1) e) (rv e).s1 (rv (vcNextParty3 e)).s1 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x2) rc.b0.x2) e) (rv e).s2 (rv (vcNextParty3 e)).s2 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x3) rc.b0.x3) e) (rv e).s3 (rv (vcNextParty3 e)).s3 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x0) rc.b1.x0) e) (rv e).s4 (rv (vcNextParty3 e)).s4 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x1) rc.b1.x1) e) (rv e).s5 (rv (vcNextParty3 e)).s5 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x2) rc.b1.x2) e) (rv e).s6 (rv (vcNextParty3 e)).s6 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x3) rc.b1.x3) e) (rv e).s7 (rv (vcNextParty3 e)).s7 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x0) rc.b2.x0) e) (rv e).s8 (rv (vcNextParty3 e)).s8 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x1) rc.b2.x1) e) (rv e).s9 (rv (vcNextParty3 e)).s9 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x2) rc.b2.x2) e) (rv e).s10 (rv (vcNextParty3 e)).s10 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x3) rc.b2.x3) e) (rv e).s11 (rv (vcNextParty3 e)).s11 = some o) := by
  unfold pairCheckExtRound vcPairAtState12 at hOk
  dsimp only at hOk
  have hAt : ∀ f : Poseidon2State12 → Goldilocks,
      vcPairAddConst e (f (st e), f (st (vcNextParty3 e))) (f rc) =
        vcPairAt (vcWireAddConst3 (fun i => f (st i)) (f rc)) e :=
    fun f => vcPairAddConst_spec (fun i => f (st i)) (f rc) e
  rw [hAt (·.b0.x0), hAt (·.b0.x1), hAt (·.b0.x2), hAt (·.b0.x3),
      hAt (·.b1.x0), hAt (·.b1.x1), hAt (·.b1.x2), hAt (·.b1.x3),
      hAt (·.b2.x0), hAt (·.b2.x1), hAt (·.b2.x2), hAt (·.b2.x3)] at hOk
  cases hs0 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc.b0.x0) e) (rv e).s0 (rv (vcNextParty3 e)).s0 with
  | none => rw [hs0] at hOk; cases hOk
  | some y0 =>
  cases hs1 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x1) rc.b0.x1) e) (rv e).s1 (rv (vcNextParty3 e)).s1 with
  | none => rw [hs0, hs1] at hOk; cases hOk
  | some y1 =>
  cases hs2 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x2) rc.b0.x2) e) (rv e).s2 (rv (vcNextParty3 e)).s2 with
  | none => rw [hs0, hs1, hs2] at hOk; cases hOk
  | some y2 =>
  cases hs3 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x3) rc.b0.x3) e) (rv e).s3 (rv (vcNextParty3 e)).s3 with
  | none => rw [hs0, hs1, hs2, hs3] at hOk; cases hOk
  | some y3 =>
  cases hs4 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x0) rc.b1.x0) e) (rv e).s4 (rv (vcNextParty3 e)).s4 with
  | none => rw [hs0, hs1, hs2, hs3, hs4] at hOk; cases hOk
  | some y4 =>
  cases hs5 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x1) rc.b1.x1) e) (rv e).s5 (rv (vcNextParty3 e)).s5 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5] at hOk; cases hOk
  | some y5 =>
  cases hs6 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x2) rc.b1.x2) e) (rv e).s6 (rv (vcNextParty3 e)).s6 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6] at hOk; cases hOk
  | some y6 =>
  cases hs7 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x3) rc.b1.x3) e) (rv e).s7 (rv (vcNextParty3 e)).s7 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at hOk; cases hOk
  | some y7 =>
  cases hs8 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x0) rc.b2.x0) e) (rv e).s8 (rv (vcNextParty3 e)).s8 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at hOk; cases hOk
  | some y8 =>
  cases hs9 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x1) rc.b2.x1) e) (rv e).s9 (rv (vcNextParty3 e)).s9 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9] at hOk; cases hOk
  | some y9 =>
  cases hs10 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x2) rc.b2.x2) e) (rv e).s10 (rv (vcNextParty3 e)).s10 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10] at hOk; cases hOk
  | some y10 =>
  cases hs11 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x3) rc.b2.x3) e) (rv e).s11 (rv (vcNextParty3 e)).s11 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at hOk; cases hOk
  | some y11 =>
    rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at hOk
    injection hOk with hPair
    rw [(pairCheckSbox_step (sv := fun i => (rv i).s0) hs0).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s1) hs1).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s2) hs2).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s3) hs3).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s4) hs4).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s5) hs5).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s6) hs6).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s7) hs7).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s8) hs8).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s9) hs9).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s10) hs10).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s11) hs11).1] at hPair
    exact ⟨hPair.symm, ⟨y0, rfl⟩, ⟨y1, rfl⟩, ⟨y2, rfl⟩, ⟨y3, rfl⟩, ⟨y4, rfl⟩, ⟨y5, rfl⟩,
      ⟨y6, rfl⟩, ⟨y7, rfl⟩, ⟨y8, rfl⟩, ⟨y9, rfl⟩, ⟨y10, rfl⟩, ⟨y11, rfl⟩⟩

private theorem vcSumState12_3_applyME (f : VcState12_3) :
    vcSumState12_3 (fun i => applyME (f i)) = applyME (vcSumState12_3 f) := by
  unfold vcSumState12_3
  rw [← applyME_add, ← applyME_add]

private theorem vcSumState12_3_applyMI (f : VcState12_3) :
    vcSumState12_3 (fun i => applyMI (f i)) = applyMI (vcSumState12_3 f) := by
  unfold vcSumState12_3
  rw [← applyMI_add, ← applyMI_add]

private theorem pairCheckExtRound_extract3 {rc : Poseidon2State12} {st : VcState12_3}
    {rv : Fin 3 → PartyExtRoundView} {o0 o1 o2 : Poseidon2State12 × Poseidon2State12}
    (h0 : pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) = some o0)
    (h1 : pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) = some o1)
    (h2 : pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) = some o2) :
    vcSumState12_3 (vcExtRoundOut3 rv) = externalRound rc (vcSumState12_3 st) := by
  obtain ⟨_, ⟨_, a0⟩, ⟨_, a1⟩, ⟨_, a2⟩, ⟨_, a3⟩, ⟨_, a4⟩, ⟨_, a5⟩,
             ⟨_, a6⟩, ⟨_, a7⟩, ⟨_, a8⟩, ⟨_, a9⟩, ⟨_, a10⟩, ⟨_, a11⟩⟩ := pairCheckExtRound_step h0
  obtain ⟨_, ⟨_, b0⟩, ⟨_, b1⟩, ⟨_, b2⟩, ⟨_, b3⟩, ⟨_, b4⟩, ⟨_, b5⟩,
             ⟨_, b6⟩, ⟨_, b7⟩, ⟨_, b8⟩, ⟨_, b9⟩, ⟨_, b10⟩, ⟨_, b11⟩⟩ := pairCheckExtRound_step h1
  obtain ⟨_, ⟨_, c0⟩, ⟨_, c1⟩, ⟨_, c2⟩, ⟨_, c3⟩, ⟨_, c4⟩, ⟨_, c5⟩,
             ⟨_, c6⟩, ⟨_, c7⟩, ⟨_, c8⟩, ⟨_, c9⟩, ⟨_, c10⟩, ⟨_, c11⟩⟩ := pairCheckExtRound_step h2
  dsimp only [vcNextParty3] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  dsimp only [vcNextParty3] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  dsimp only [vcNextParty3] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
  unfold vcExtRoundOut3
  rw [vcSumState12_3_applyME, externalRound_eq]
  congr 1
  rw [vcSumState12_3_lanes, sboxState12_eq, state12Add_eq, vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, lane4Add_eq]
  rw [pairCheckSbox_extract3 (sv := fun i => (rv i).s0) a0 b0 c0,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s1) a1 b1 c1,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s2) a2 b2 c2,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s3) a3 b3 c3,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s4) a4 b4 c4,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s5) a5 b5 c5,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s6) a6 b6 c6,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s7) a7 b7 c7,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s8) a8 b8 c8,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s9) a9 b9 c9,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s10) a10 b10 c10,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s11) a11 b11 c11]
  simp only [vcSum3_addConst]

def pairCheckIntRound (e : Fin 3) (rc : Goldilocks)
    (vE vE1 : PartySboxView) (st : Poseidon2State12 × Poseidon2State12) :
    Option (Poseidon2State12 × Poseidon2State12) :=
  match pairCheckSbox (vcPairAddConst e (st.1.b0.x0, st.2.b0.x0) rc) vE vE1 with
  | none => none
  | some y0 =>
    some (applyMI ⟨⟨y0.1, st.1.b0.x1, st.1.b0.x2, st.1.b0.x3⟩, st.1.b1, st.1.b2⟩,
          applyMI ⟨⟨y0.2, st.2.b0.x1, st.2.b0.x2, st.2.b0.x3⟩, st.2.b1, st.2.b2⟩)

def vcIntRoundOut3 (st : VcState12_3) (sv : Fin 3 → PartySboxView) : VcState12_3 :=
  fun i => applyMI ⟨⟨(sv i).g4.out, (st i).b0.x1, (st i).b0.x2, (st i).b0.x3⟩, (st i).b1, (st i).b2⟩

def honestIntRound3 (rc : Goldilocks) (st : VcState12_3) (sc : Fin 3 → SboxCoins) :
    (Fin 3 → PartySboxView) × VcState12_3 :=
  let r0 := honestSboxView3 (vcWireAddConst3 (fun i => (st i).b0.x0) rc) sc
  (r0.1, vcIntRoundOut3 st r0.1)

private theorem pairCheckIntRound_honest (rc : Goldilocks) (st : VcState12_3)
    (sc : Fin 3 → SboxCoins) (e : Fin 3) :
    pairCheckIntRound e rc ((honestIntRound3 rc st sc).1 e) ((honestIntRound3 rc st sc).1 (vcNextParty3 e))
      (vcPairAtState12 st e) = some (vcPairAtState12 (honestIntRound3 rc st sc).2 e) := by
  unfold pairCheckIntRound honestIntRound3 vcPairAtState12 vcIntRoundOut3
  dsimp only
  have hAdd : vcPairAddConst e ((st e).b0.x0, (st (vcNextParty3 e)).b0.x0) rc =
      vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e :=
    vcPairAddConst_spec (fun i => (st i).b0.x0) rc e
  rw [hAdd, pairCheckSbox_honest]
  rfl

private theorem pairCheckIntRound_step {rc : Goldilocks} {st : VcState12_3}
    {sv : Fin 3 → PartySboxView} {e : Fin 3} {outSt : Poseidon2State12 × Poseidon2State12}
    (hOk : pairCheckIntRound e rc (sv e) (sv (vcNextParty3 e)) (vcPairAtState12 st e) = some outSt) :
    outSt = vcPairAtState12 (vcIntRoundOut3 st sv) e ∧
    ∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e) (sv e) (sv (vcNextParty3 e)) = some o := by
  unfold pairCheckIntRound vcPairAtState12 at hOk
  dsimp only at hOk
  have hAdd : vcPairAddConst e ((st e).b0.x0, (st (vcNextParty3 e)).b0.x0) rc =
      vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e :=
    vcPairAddConst_spec (fun i => (st i).b0.x0) rc e
  rw [hAdd] at hOk
  cases hs0 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e) (sv e) (sv (vcNextParty3 e)) with
  | none => rw [hs0] at hOk; cases hOk
  | some y0 =>
    rw [hs0] at hOk
    injection hOk with hPair
    rw [(pairCheckSbox_step hs0).1] at hPair
    exact ⟨hPair.symm, ⟨y0, rfl⟩⟩

private theorem pairCheckIntRound_extract3 {rc : Goldilocks} {st : VcState12_3}
    {sv : Fin 3 → PartySboxView} {o0 o1 o2 : Poseidon2State12 × Poseidon2State12}
    (h0 : pairCheckIntRound 0 rc (sv 0) (sv 1) (vcPairAtState12 st 0) = some o0)
    (h1 : pairCheckIntRound 1 rc (sv 1) (sv 2) (vcPairAtState12 st 1) = some o1)
    (h2 : pairCheckIntRound 2 rc (sv 2) (sv 0) (vcPairAtState12 st 2) = some o2) :
    vcSumState12_3 (vcIntRoundOut3 st sv) = internalRound rc (vcSumState12_3 st) := by
  obtain ⟨_, ⟨_, a0⟩⟩ := pairCheckIntRound_step h0
  obtain ⟨_, ⟨_, b0⟩⟩ := pairCheckIntRound_step h1
  obtain ⟨_, ⟨_, c0⟩⟩ := pairCheckIntRound_step h2
  dsimp only [vcNextParty3] at a0 b0 c0
  unfold vcIntRoundOut3
  rw [vcSumState12_3_applyMI, internalRound_eq]
  congr 1
  rw [vcSumState12_3_lanes, vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq]
  rw [pairCheckSbox_extract3 a0 b0 c0, vcSum3_addConst]

def pairCheckExtRounds (e : Fin 3) :
    List Poseidon2State12 → List PartyExtRoundView → List PartyExtRoundView →
    Poseidon2State12 × Poseidon2State12 → Option (Poseidon2State12 × Poseidon2State12)
  | [], [], [], st => some st
  | rc :: rcs, vE :: vsE, vE1 :: vsE1, st =>
    match pairCheckExtRound e rc vE vE1 st with
    | none => none
    | some st' => pairCheckExtRounds e rcs vsE vsE1 st'
  | _, _, _, _ => none

def pairCheckIntRounds (e : Fin 3) :
    List Goldilocks → List PartySboxView → List PartySboxView →
    Poseidon2State12 × Poseidon2State12 → Option (Poseidon2State12 × Poseidon2State12)
  | [], [], [], st => some st
  | rc :: rcs, vE :: vsE, vE1 :: vsE1, st =>
    match pairCheckIntRound e rc vE vE1 st with
    | none => none
    | some st' => pairCheckIntRounds e rcs vsE vsE1 st'
  | _, _, _, _ => none

def honestExtRounds3 :
    (rcs : List Poseidon2State12) → VcState12_3 → (Fin 3 → Vec ExtRoundCoins rcs.length) →
    (Fin 3 → List PartyExtRoundView) × VcState12_3
  | [], st, _ => (fun _ => [], st)
  | rc :: rcs, st, cs =>
    let rHead := honestExtRound3 rc st (fun i => (cs i).head)
    let rTail := honestExtRounds3 rcs rHead.2 (fun i => (cs i).tail)
    (fun i => rHead.1 i :: rTail.1 i, rTail.2)

def honestIntRounds3 :
    (rcs : List Goldilocks) → VcState12_3 → (Fin 3 → Vec SboxCoins rcs.length) →
    (Fin 3 → List PartySboxView) × VcState12_3
  | [], st, _ => (fun _ => [], st)
  | rc :: rcs, st, cs =>
    let rHead := honestIntRound3 rc st (fun i => (cs i).head)
    let rTail := honestIntRounds3 rcs rHead.2 (fun i => (cs i).tail)
    (fun i => rHead.1 i :: rTail.1 i, rTail.2)

def extractExtRoundsCoins :
    (rcs : List Poseidon2State12) → List PartyExtRoundView → Option (Vec ExtRoundCoins rcs.length)
  | [], [] => some .nil
  | _ :: rcs, v :: vsl => (extractExtRoundsCoins rcs vsl).map (Vec.cons (extractExtRoundCoins v))
  | _, _ => none

def extractIntRoundsCoins :
    (rcs : List Goldilocks) → List PartySboxView → Option (Vec SboxCoins rcs.length)
  | [], [] => some .nil
  | _ :: rcs, v :: vsl => (extractIntRoundsCoins rcs vsl).map (Vec.cons (extractSboxCoins v))
  | _, _ => none

private theorem extractExtRoundsCoins_honest :
    ∀ (rcs : List Poseidon2State12) (st : VcState12_3) (cs : Fin 3 → Vec ExtRoundCoins rcs.length) (i : Fin 3),
      extractExtRoundsCoins rcs ((honestExtRounds3 rcs st cs).1 i) = some (cs i)
  | [], _, cs, i => by cases cs i; rfl
  | rc :: rcs, st, cs, i => by
    dsimp only [honestExtRounds3, extractExtRoundsCoins]
    rw [extractExtRoundsCoins_honest rcs (honestExtRound3 rc st (fun j => (cs j).head)).2 (fun j => (cs j).tail) i]
    dsimp only [Option.map]
    rw [extractExtRoundCoins_honest, Vec.eta_cons]

private theorem extractIntRoundsCoins_honest :
    ∀ (rcs : List Goldilocks) (st : VcState12_3) (cs : Fin 3 → Vec SboxCoins rcs.length) (i : Fin 3),
      extractIntRoundsCoins rcs ((honestIntRounds3 rcs st cs).1 i) = some (cs i)
  | [], _, cs, i => by cases cs i; rfl
  | rc :: rcs, st, cs, i => by
    dsimp only [honestIntRounds3, extractIntRoundsCoins]
    rw [extractIntRoundsCoins_honest rcs (honestIntRound3 rc st (fun j => (cs j).head)).2 (fun j => (cs j).tail) i]
    dsimp only [Option.map]
    change some (Vec.cons (cs i).head (cs i).tail) = some (cs i)
    rw [Vec.eta_cons]

private theorem pairCheckExtRounds_honest :
    ∀ (rcs : List Poseidon2State12) (st : VcState12_3) (cs : Fin 3 → Vec ExtRoundCoins rcs.length) (e : Fin 3),
      pairCheckExtRounds e rcs ((honestExtRounds3 rcs st cs).1 e)
        ((honestExtRounds3 rcs st cs).1 (vcNextParty3 e)) (vcPairAtState12 st e) =
        some (vcPairAtState12 (honestExtRounds3 rcs st cs).2 e)
  | [], _, _, _ => rfl
  | rc :: rcs, st, cs, e => by
    dsimp only [honestExtRounds3, pairCheckExtRounds]
    rw [pairCheckExtRound_honest]
    exact pairCheckExtRounds_honest rcs (honestExtRound3 rc st (fun i => (cs i).head)).2 (fun i => (cs i).tail) e

private theorem pairCheckIntRounds_honest :
    ∀ (rcs : List Goldilocks) (st : VcState12_3) (cs : Fin 3 → Vec SboxCoins rcs.length) (e : Fin 3),
      pairCheckIntRounds e rcs ((honestIntRounds3 rcs st cs).1 e)
        ((honestIntRounds3 rcs st cs).1 (vcNextParty3 e)) (vcPairAtState12 st e) =
        some (vcPairAtState12 (honestIntRounds3 rcs st cs).2 e)
  | [], _, _, _ => rfl
  | rc :: rcs, st, cs, e => by
    dsimp only [honestIntRounds3, pairCheckIntRounds]
    rw [pairCheckIntRound_honest]
    exact pairCheckIntRounds_honest rcs (honestIntRound3 rc st (fun i => (cs i).head)).2 (fun i => (cs i).tail) e

private theorem pairCheckExtRounds_extract3 :
    ∀ (rcs : List Poseidon2State12) (st : VcState12_3) (vsl : Fin 3 → List PartyExtRoundView)
      {o0 o1 o2 : Poseidon2State12 × Poseidon2State12},
      pairCheckExtRounds 0 rcs (vsl 0) (vsl 1) (vcPairAtState12 st 0) = some o0 →
      pairCheckExtRounds 1 rcs (vsl 1) (vsl 2) (vcPairAtState12 st 1) = some o1 →
      pairCheckExtRounds 2 rcs (vsl 2) (vsl 0) (vcPairAtState12 st 2) = some o2 →
      ∃ stOut : VcState12_3,
        o0 = vcPairAtState12 stOut 0 ∧
        o1 = vcPairAtState12 stOut 1 ∧
        o2 = vcPairAtState12 stOut 2 ∧
        vcSumState12_3 stOut = runRounds externalRound rcs (vcSumState12_3 st)
  | [], st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | cons _ _ => rw [hv0] at h0; cases h0
    | nil =>
      cases hv1 : vsl 1 with
      | cons _ _ => rw [hv0, hv1] at h0; cases h0
      | nil =>
        cases hv2 : vsl 2 with
        | cons _ _ => rw [hv1, hv2] at h1; cases h1
        | nil =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckExtRounds] at h0 h1 h2
          injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
          rw [runRounds_nil]
          exact ⟨st, ho0.symm, ho1.symm, ho2.symm, rfl⟩
  | rc :: rcs, st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | nil => rw [hv0] at h0; cases h0
    | cons r0 rs0 =>
      cases hv1 : vsl 1 with
      | nil => rw [hv0, hv1] at h0; cases h0
      | cons r1 rs1 =>
        cases hv2 : vsl 2 with
        | nil => rw [hv1, hv2] at h1; cases h1
        | cons r2 rs2 =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckExtRounds] at h0 h1 h2
          let rv : Fin 3 → PartyExtRoundView := fun | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2
          let rs : Fin 3 → List PartyExtRoundView := fun | ⟨0, _⟩ => rs0 | ⟨1, _⟩ => rs1 | ⟨2, _⟩ => rs2
          cases hm0 : pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with
          | none => change (match pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => _) = some o0 at h0; rw [hm0] at h0; cases h0
          | some m0 =>
            cases hm1 : pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with
            | none => change (match pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => _) = some o1 at h1; rw [hm1] at h1; cases h1
            | some m1 =>
              cases hm2 : pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with
              | none => change (match pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => _) = some o2 at h2; rw [hm2] at h2; cases h2
              | some m2 =>
                change (match pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => pairCheckExtRounds 0 rcs (rs 0) (rs 1) st') = some o0 at h0
                change (match pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => pairCheckExtRounds 1 rcs (rs 1) (rs 2) st') = some o1 at h1
                change (match pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => pairCheckExtRounds 2 rcs (rs 2) (rs 0) st') = some o2 at h2
                rw [hm0] at h0; rw [hm1] at h1; rw [hm2] at h2
                rw [(pairCheckExtRound_step hm0).1] at h0
                rw [(pairCheckExtRound_step hm1).1] at h1
                rw [(pairCheckExtRound_step hm2).1] at h2
                obtain ⟨stOut, e0, e1, e2, hSum⟩ :=
                  pairCheckExtRounds_extract3 rcs (vcExtRoundOut3 rv) rs h0 h1 h2
                rw [runRounds_cons, ← pairCheckExtRound_extract3 hm0 hm1 hm2]
                exact ⟨stOut, e0, e1, e2, hSum⟩

private theorem pairCheckIntRounds_extract3 :
    ∀ (rcs : List Goldilocks) (st : VcState12_3) (vsl : Fin 3 → List PartySboxView)
      {o0 o1 o2 : Poseidon2State12 × Poseidon2State12},
      pairCheckIntRounds 0 rcs (vsl 0) (vsl 1) (vcPairAtState12 st 0) = some o0 →
      pairCheckIntRounds 1 rcs (vsl 1) (vsl 2) (vcPairAtState12 st 1) = some o1 →
      pairCheckIntRounds 2 rcs (vsl 2) (vsl 0) (vcPairAtState12 st 2) = some o2 →
      ∃ stOut : VcState12_3,
        o0 = vcPairAtState12 stOut 0 ∧
        o1 = vcPairAtState12 stOut 1 ∧
        o2 = vcPairAtState12 stOut 2 ∧
        vcSumState12_3 stOut = runRounds internalRound rcs (vcSumState12_3 st)
  | [], st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | cons _ _ => rw [hv0] at h0; cases h0
    | nil =>
      cases hv1 : vsl 1 with
      | cons _ _ => rw [hv0, hv1] at h0; cases h0
      | nil =>
        cases hv2 : vsl 2 with
        | cons _ _ => rw [hv1, hv2] at h1; cases h1
        | nil =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckIntRounds] at h0 h1 h2
          injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
          rw [runRounds_nil]
          exact ⟨st, ho0.symm, ho1.symm, ho2.symm, rfl⟩
  | rc :: rcs, st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | nil => rw [hv0] at h0; cases h0
    | cons r0 rs0 =>
      cases hv1 : vsl 1 with
      | nil => rw [hv0, hv1] at h0; cases h0
      | cons r1 rs1 =>
        cases hv2 : vsl 2 with
        | nil => rw [hv1, hv2] at h1; cases h1
        | cons r2 rs2 =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckIntRounds] at h0 h1 h2
          let rv : Fin 3 → PartySboxView := fun | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2
          let rs : Fin 3 → List PartySboxView := fun | ⟨0, _⟩ => rs0 | ⟨1, _⟩ => rs1 | ⟨2, _⟩ => rs2
          cases hm0 : pairCheckIntRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with
          | none => change (match pairCheckIntRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => _) = some o0 at h0; rw [hm0] at h0; cases h0
          | some m0 =>
            cases hm1 : pairCheckIntRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with
            | none => change (match pairCheckIntRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => _) = some o1 at h1; rw [hm1] at h1; cases h1
            | some m1 =>
              cases hm2 : pairCheckIntRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with
              | none => change (match pairCheckIntRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => _) = some o2 at h2; rw [hm2] at h2; cases h2
              | some m2 =>
                change (match pairCheckIntRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => pairCheckIntRounds 0 rcs (rs 0) (rs 1) st') = some o0 at h0
                change (match pairCheckIntRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => pairCheckIntRounds 1 rcs (rs 1) (rs 2) st') = some o1 at h1
                change (match pairCheckIntRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => pairCheckIntRounds 2 rcs (rs 2) (rs 0) st') = some o2 at h2
                rw [hm0] at h0; rw [hm1] at h1; rw [hm2] at h2
                rw [(pairCheckIntRound_step hm0).1] at h0
                rw [(pairCheckIntRound_step hm1).1] at h1
                rw [(pairCheckIntRound_step hm2).1] at h2
                obtain ⟨stOut, e0, e1, e2, hSum⟩ :=
                  pairCheckIntRounds_extract3 rcs (vcIntRoundOut3 st rv) rs h0 h1 h2
                rw [runRounds_cons, ← pairCheckIntRound_extract3 hm0 hm1 hm2]
                exact ⟨stOut, e0, e1, e2, hSum⟩

structure PartyPerm12View where
  initExt : List PartyExtRoundView
  internal : List PartySboxView
  termExt : List PartyExtRoundView
  deriving DecidableEq, Repr

def extractPerm12Coins (pv : PartyPerm12View) : Option Perm12Coins :=
  match extractExtRoundsCoins poseidon2InitialExtConsts pv.initExt,
        extractIntRoundsCoins poseidon2InternalConsts pv.internal,
        extractExtRoundsCoins poseidon2TerminalExtConsts pv.termExt with
  | some c1, some c2, some c3 => some ⟨c1, c2, c3⟩
  | _, _, _ => none

def pairCheckRawPerm12 (e : Fin 3) (vE vE1 : PartyPerm12View)
    (st : Poseidon2State12 × Poseidon2State12) : Option (Poseidon2State12 × Poseidon2State12) :=
  let s0 := (applyME st.1, applyME st.2)
  match pairCheckExtRounds e poseidon2InitialExtConsts vE.initExt vE1.initExt s0 with
  | none => none
  | some s1 =>
    match pairCheckIntRounds e poseidon2InternalConsts vE.internal vE1.internal s1 with
    | none => none
    | some s2 => pairCheckExtRounds e poseidon2TerminalExtConsts vE.termExt vE1.termExt s2

def honestRawPerm12_3 (st : VcState12_3) (pc : Fin 3 → Perm12Coins) :
    (Fin 3 → PartyPerm12View) × VcState12_3 :=
  let s0 : VcState12_3 := fun i => applyME (st i)
  let r1 := honestExtRounds3 poseidon2InitialExtConsts s0 (fun i => (pc i).initExt)
  let r2 := honestIntRounds3 poseidon2InternalConsts r1.2 (fun i => (pc i).internal)
  let r3 := honestExtRounds3 poseidon2TerminalExtConsts r2.2 (fun i => (pc i).termExt)
  (fun i => ⟨r1.1 i, r2.1 i, r3.1 i⟩, r3.2)

private theorem extractPerm12Coins_honest (st : VcState12_3) (pc : Fin 3 → Perm12Coins) (i : Fin 3) :
    extractPerm12Coins ((honestRawPerm12_3 st pc).1 i) = some (pc i) := by
  unfold extractPerm12Coins honestRawPerm12_3
  dsimp only
  rw [extractExtRoundsCoins_honest, extractIntRoundsCoins_honest, extractExtRoundsCoins_honest]

private theorem pairCheckRawPerm12_honest (st : VcState12_3) (pc : Fin 3 → Perm12Coins) (e : Fin 3) :
    pairCheckRawPerm12 e ((honestRawPerm12_3 st pc).1 e) ((honestRawPerm12_3 st pc).1 (vcNextParty3 e))
      (vcPairAtState12 st e) = some (vcPairAtState12 (honestRawPerm12_3 st pc).2 e) := by
  unfold pairCheckRawPerm12 honestRawPerm12_3
  dsimp only
  have hs0 : (applyME (vcPairAtState12 st e).1, applyME (vcPairAtState12 st e).2) =
      vcPairAtState12 (fun i => applyME (st i)) e := rfl
  rw [hs0, pairCheckExtRounds_honest]; dsimp only
  rw [pairCheckIntRounds_honest]; dsimp only
  rw [pairCheckExtRounds_honest]

private theorem pairCheckRawPerm12_extract3 {st : VcState12_3} {pv : Fin 3 → PartyPerm12View}
    {o0 o1 o2 : Poseidon2State12 × Poseidon2State12}
    (h0 : pairCheckRawPerm12 0 (pv 0) (pv 1) (vcPairAtState12 st 0) = some o0)
    (h1 : pairCheckRawPerm12 1 (pv 1) (pv 2) (vcPairAtState12 st 1) = some o1)
    (h2 : pairCheckRawPerm12 2 (pv 2) (pv 0) (vcPairAtState12 st 2) = some o2) :
    ∃ stOut : VcState12_3,
      o0 = vcPairAtState12 stOut 0 ∧
      o1 = vcPairAtState12 stOut 1 ∧
      o2 = vcPairAtState12 stOut 2 ∧
      vcSumState12_3 stOut = poseidon2Perm12 (vcSumState12_3 st) := by
  unfold pairCheckRawPerm12 at h0 h1 h2
  let s0 : VcState12_3 := fun i => applyME (st i)
  change (match pairCheckExtRounds 0 poseidon2InitialExtConsts (pv 0).initExt (pv 1).initExt (vcPairAtState12 s0 0) with | none => none | some s1 => _) = some o0 at h0
  change (match pairCheckExtRounds 1 poseidon2InitialExtConsts (pv 1).initExt (pv 2).initExt (vcPairAtState12 s0 1) with | none => none | some s1 => _) = some o1 at h1
  change (match pairCheckExtRounds 2 poseidon2InitialExtConsts (pv 2).initExt (pv 0).initExt (vcPairAtState12 s0 2) with | none => none | some s1 => _) = some o2 at h2
  cases a0 : pairCheckExtRounds 0 poseidon2InitialExtConsts (pv 0).initExt (pv 1).initExt (vcPairAtState12 s0 0) with
  | none => rw [a0] at h0; cases h0
  | some u0 =>
  cases a1 : pairCheckExtRounds 1 poseidon2InitialExtConsts (pv 1).initExt (pv 2).initExt (vcPairAtState12 s0 1) with
  | none => rw [a1] at h1; cases h1
  | some u1 =>
  cases a2 : pairCheckExtRounds 2 poseidon2InitialExtConsts (pv 2).initExt (pv 0).initExt (vcPairAtState12 s0 2) with
  | none => rw [a2] at h2; cases h2
  | some u2 =>
    rw [a0] at h0; rw [a1] at h1; rw [a2] at h2
    obtain ⟨st1, hu0, hu1, hu2, hSum1⟩ :=
      pairCheckExtRounds_extract3 poseidon2InitialExtConsts s0 (fun i => (pv i).initExt) a0 a1 a2
    rw [hu0] at h0; rw [hu1] at h1; rw [hu2] at h2
    dsimp only at h0 h1 h2
    cases b0 : pairCheckIntRounds 0 poseidon2InternalConsts (pv 0).internal (pv 1).internal (vcPairAtState12 st1 0) with
    | none => rw [b0] at h0; cases h0
    | some v0 =>
    cases b1 : pairCheckIntRounds 1 poseidon2InternalConsts (pv 1).internal (pv 2).internal (vcPairAtState12 st1 1) with
    | none => rw [b1] at h1; cases h1
    | some v1 =>
    cases b2 : pairCheckIntRounds 2 poseidon2InternalConsts (pv 2).internal (pv 0).internal (vcPairAtState12 st1 2) with
    | none => rw [b2] at h2; cases h2
    | some v2 =>
      rw [b0] at h0; rw [b1] at h1; rw [b2] at h2
      obtain ⟨st2, hv0, hv1, hv2, hSum2⟩ :=
        pairCheckIntRounds_extract3 poseidon2InternalConsts st1 (fun i => (pv i).internal) b0 b1 b2
      rw [hv0] at h0; rw [hv1] at h1; rw [hv2] at h2
      dsimp only at h0 h1 h2
      obtain ⟨st3, hw0, hw1, hw2, hSum3⟩ :=
        pairCheckExtRounds_extract3 poseidon2TerminalExtConsts st2 (fun i => (pv i).termExt) h0 h1 h2
      refine ⟨st3, hw0, hw1, hw2, ?_⟩
      unfold poseidon2Perm12
      dsimp only
      rw [hSum3, hSum2, hSum1, vcSumState12_3_applyME]

/-- Single party's view for 3-permutation rate-6/capacity-6 `absorbRate6Sponge3` (`blind_vc.rs:390-405`). -/
structure PartySponge3PermView where
  perm1 : PartyPerm12View
  perm2 : PartyPerm12View
  perm3 : PartyPerm12View
  deriving DecidableEq, Repr

def extractSponge3Coins (sv : PartySponge3PermView) : Option Sponge3Coins :=
  match extractPerm12Coins sv.perm1, extractPerm12Coins sv.perm2, extractPerm12Coins sv.perm3 with
  | some c1, some c2, some c3 => some ⟨c1, c2, c3⟩
  | _, _, _ => none

def pairCheckSponge3Perm (e : Fin 3) (vE vE1 : PartySponge3PermView)
    (c0 c1 c2 : Lane6 × Lane6) : Option (Lane6 × Lane6) :=
  let s1 := (mkState12Of6 c0.1 lane6Zero, mkState12Of6 c0.2 lane6Zero)
  match pairCheckRawPerm12 e vE.perm1 vE1.perm1 s1 with
  | none => none
  | some p1 =>
    let s2 := (mkState12Of6 (lane6Add (state12Rate6 p1.1) c1.1) (state12Cap6 p1.1),
               mkState12Of6 (lane6Add (state12Rate6 p1.2) c1.2) (state12Cap6 p1.2))
    match pairCheckRawPerm12 e vE.perm2 vE1.perm2 s2 with
    | none => none
    | some p2 =>
      let s3 := (mkState12Of6 (lane6Add (state12Rate6 p2.1) c2.1) (state12Cap6 p2.1),
                 mkState12Of6 (lane6Add (state12Rate6 p2.2) c2.2) (state12Cap6 p2.2))
      match pairCheckRawPerm12 e vE.perm3 vE1.perm3 s3 with
      | none => none
      | some p3 => some (state12Rate6 p3.1, state12Rate6 p3.2)

def honestSponge3Perm3 (c0 c1 c2 : VcLane6_3) (sc : Fin 3 → Sponge3Coins) :
    (Fin 3 → PartySponge3PermView) × VcLane6_3 :=
  let s1 : VcState12_3 := fun i => mkState12Of6 (c0 i) lane6Zero
  let r1 := honestRawPerm12_3 s1 (fun i => (sc i).perm1)
  let s2 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (r1.2 i)) (c1 i)) (state12Cap6 (r1.2 i))
  let r2 := honestRawPerm12_3 s2 (fun i => (sc i).perm2)
  let s3 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (r2.2 i)) (c2 i)) (state12Cap6 (r2.2 i))
  let r3 := honestRawPerm12_3 s3 (fun i => (sc i).perm3)
  (fun i => ⟨r1.1 i, r2.1 i, r3.1 i⟩, fun i => state12Rate6 (r3.2 i))

private theorem extractSponge3Coins_honest (c0 c1 c2 : VcLane6_3) (sc : Fin 3 → Sponge3Coins) (i : Fin 3) :
    extractSponge3Coins ((honestSponge3Perm3 c0 c1 c2 sc).1 i) = some (sc i) := by
  unfold extractSponge3Coins honestSponge3Perm3
  dsimp only
  rw [extractPerm12Coins_honest, extractPerm12Coins_honest, extractPerm12Coins_honest]

private theorem pairCheckSponge3Perm_honest (c0 c1 c2 : VcLane6_3)
    (sc : Fin 3 → Sponge3Coins) (e : Fin 3) :
    pairCheckSponge3Perm e ((honestSponge3Perm3 c0 c1 c2 sc).1 e)
      ((honestSponge3Perm3 c0 c1 c2 sc).1 (vcNextParty3 e))
      (vcPairAtLane6 c0 e) (vcPairAtLane6 c1 e) (vcPairAtLane6 c2 e) =
      some (vcPairAtLane6 (honestSponge3Perm3 c0 c1 c2 sc).2 e) := by
  unfold pairCheckSponge3Perm honestSponge3Perm3 vcPairAtLane6
  dsimp only
  have hs1 : (mkState12Of6 (c0 e) lane6Zero, mkState12Of6 (c0 (vcNextParty3 e)) lane6Zero) =
      vcPairAtState12 (fun i => mkState12Of6 (c0 i) lane6Zero) e := rfl
  rw [hs1, pairCheckRawPerm12_honest]; dsimp only
  let p1 := (honestRawPerm12_3 (fun i => mkState12Of6 (c0 i) lane6Zero) (fun i => (sc i).perm1)).2
  have hs2 : (mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p1 e).1) (c1 e)) (state12Cap6 (vcPairAtState12 p1 e).1),
              mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p1 e).2) (c1 (vcNextParty3 e))) (state12Cap6 (vcPairAtState12 p1 e).2)) =
      vcPairAtState12 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))) e := rfl
  rw [hs2, pairCheckRawPerm12_honest]; dsimp only
  let p2 := (honestRawPerm12_3 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))) (fun i => (sc i).perm2)).2
  have hs3 : (mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p2 e).1) (c2 e)) (state12Cap6 (vcPairAtState12 p2 e).1),
              mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p2 e).2) (c2 (vcNextParty3 e))) (state12Cap6 (vcPairAtState12 p2 e).2)) =
      vcPairAtState12 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p2 i)) (c2 i)) (state12Cap6 (p2 i))) e := rfl
  rw [hs3, pairCheckRawPerm12_honest]
  rfl

private theorem pairCheckSponge3Perm_extract3 {c0 c1 c2 : VcLane6_3}
    {sv : Fin 3 → PartySponge3PermView} {o0 o1 o2 : Lane6 × Lane6}
    (h0 : pairCheckSponge3Perm 0 (sv 0) (sv 1) (vcPairAtLane6 c0 0) (vcPairAtLane6 c1 0) (vcPairAtLane6 c2 0) = some o0)
    (h1 : pairCheckSponge3Perm 1 (sv 1) (sv 2) (vcPairAtLane6 c0 1) (vcPairAtLane6 c1 1) (vcPairAtLane6 c2 1) = some o1)
    (h2 : pairCheckSponge3Perm 2 (sv 2) (sv 0) (vcPairAtLane6 c0 2) (vcPairAtLane6 c1 2) (vcPairAtLane6 c2 2) = some o2) :
    ∃ out6 : VcLane6_3,
      o0 = vcPairAtLane6 out6 0 ∧
      o1 = vcPairAtLane6 out6 1 ∧
      o2 = vcPairAtLane6 out6 2 ∧
      vcSumLane6_3 out6 =
        state12Rate6 (absorbRate6Sponge3 (vcSumLane6_3 c0) (vcSumLane6_3 c1) (vcSumLane6_3 c2)) := by
  unfold pairCheckSponge3Perm at h0 h1 h2
  let s1 : VcState12_3 := fun i => mkState12Of6 (c0 i) lane6Zero
  change (match pairCheckRawPerm12 0 (sv 0).perm1 (sv 1).perm1 (vcPairAtState12 s1 0) with | none => none | some p1 => _) = some o0 at h0
  change (match pairCheckRawPerm12 1 (sv 1).perm1 (sv 2).perm1 (vcPairAtState12 s1 1) with | none => none | some p1 => _) = some o1 at h1
  change (match pairCheckRawPerm12 2 (sv 2).perm1 (sv 0).perm1 (vcPairAtState12 s1 2) with | none => none | some p1 => _) = some o2 at h2
  cases a0 : pairCheckRawPerm12 0 (sv 0).perm1 (sv 1).perm1 (vcPairAtState12 s1 0) with
  | none => rw [a0] at h0; cases h0
  | some u0 =>
  cases a1 : pairCheckRawPerm12 1 (sv 1).perm1 (sv 2).perm1 (vcPairAtState12 s1 1) with
  | none => rw [a1] at h1; cases h1
  | some u1 =>
  cases a2 : pairCheckRawPerm12 2 (sv 2).perm1 (sv 0).perm1 (vcPairAtState12 s1 2) with
  | none => rw [a2] at h2; cases h2
  | some u2 =>
    rw [a0] at h0; rw [a1] at h1; rw [a2] at h2
    obtain ⟨p1, hu0, hu1, hu2, hSum1⟩ :=
      pairCheckRawPerm12_extract3 (pv := fun i => (sv i).perm1) a0 a1 a2
    rw [hu0] at h0; rw [hu1] at h1; rw [hu2] at h2
    dsimp only at h0 h1 h2
    let s2 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))
    change (match pairCheckRawPerm12 0 (sv 0).perm2 (sv 1).perm2 (vcPairAtState12 s2 0) with | none => none | some p2 => _) = some o0 at h0
    change (match pairCheckRawPerm12 1 (sv 1).perm2 (sv 2).perm2 (vcPairAtState12 s2 1) with | none => none | some p2 => _) = some o1 at h1
    change (match pairCheckRawPerm12 2 (sv 2).perm2 (sv 0).perm2 (vcPairAtState12 s2 2) with | none => none | some p2 => _) = some o2 at h2
    cases b0 : pairCheckRawPerm12 0 (sv 0).perm2 (sv 1).perm2 (vcPairAtState12 s2 0) with
    | none => rw [b0] at h0; cases h0
    | some v0 =>
    cases b1 : pairCheckRawPerm12 1 (sv 1).perm2 (sv 2).perm2 (vcPairAtState12 s2 1) with
    | none => rw [b1] at h1; cases h1
    | some v1 =>
    cases b2 : pairCheckRawPerm12 2 (sv 2).perm2 (sv 0).perm2 (vcPairAtState12 s2 2) with
    | none => rw [b2] at h2; cases h2
    | some v2 =>
      rw [b0] at h0; rw [b1] at h1; rw [b2] at h2
      obtain ⟨p2, hv0, hv1, hv2, hSum2⟩ :=
        pairCheckRawPerm12_extract3 (pv := fun i => (sv i).perm2) b0 b1 b2
      rw [hv0] at h0; rw [hv1] at h1; rw [hv2] at h2
      dsimp only at h0 h1 h2
      let s3 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (p2 i)) (c2 i)) (state12Cap6 (p2 i))
      change (match pairCheckRawPerm12 0 (sv 0).perm3 (sv 1).perm3 (vcPairAtState12 s3 0) with | none => none | some p3 => _) = some o0 at h0
      change (match pairCheckRawPerm12 1 (sv 1).perm3 (sv 2).perm3 (vcPairAtState12 s3 1) with | none => none | some p3 => _) = some o1 at h1
      change (match pairCheckRawPerm12 2 (sv 2).perm3 (sv 0).perm3 (vcPairAtState12 s3 2) with | none => none | some p3 => _) = some o2 at h2
      cases d0 : pairCheckRawPerm12 0 (sv 0).perm3 (sv 1).perm3 (vcPairAtState12 s3 0) with
      | none => rw [d0] at h0; cases h0
      | some w0 =>
      cases d1 : pairCheckRawPerm12 1 (sv 1).perm3 (sv 2).perm3 (vcPairAtState12 s3 1) with
      | none => rw [d1] at h1; cases h1
      | some w1 =>
      cases d2 : pairCheckRawPerm12 2 (sv 2).perm3 (sv 0).perm3 (vcPairAtState12 s3 2) with
      | none => rw [d2] at h2; cases h2
      | some w2 =>
        rw [d0] at h0; rw [d1] at h1; rw [d2] at h2
        obtain ⟨p3, hw0, hw1, hw2, hSum3⟩ :=
          pairCheckRawPerm12_extract3 (pv := fun i => (sv i).perm3) d0 d1 d2
        rw [hw0] at h0; rw [hw1] at h1; rw [hw2] at h2
        injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
        refine ⟨fun i => state12Rate6 (p3 i), ho0.symm, ho1.symm, ho2.symm, ?_⟩
        rw [← state12Rate6_vcSum, hSum3]
        have hs1Eq : vcSumState12_3 s1 = mkState12Of6 (vcSumLane6_3 c0) lane6Zero := by
          dsimp only [s1]; rw [vcSumState12_3_of6, vcSumLane6_3_zero]
        have hs2Eq : vcSumState12_3 s2 =
            mkState12Of6 (lane6Add (state12Rate6 (vcSumState12_3 p1)) (vcSumLane6_3 c1))
              (state12Cap6 (vcSumState12_3 p1)) := by
          dsimp only [s2]
          rw [vcSumState12_3_of6, vcSumLane6_3_add, ← state12Rate6_vcSum, ← state12Cap6_vcSum]
        have hs3Eq : vcSumState12_3 s3 =
            mkState12Of6 (lane6Add (state12Rate6 (vcSumState12_3 p2)) (vcSumLane6_3 c2))
              (state12Cap6 (vcSumState12_3 p2)) := by
          dsimp only [s3]
          rw [vcSumState12_3_of6, vcSumLane6_3_add, ← state12Rate6_vcSum, ← state12Cap6_vcSum]
        rw [hs3Eq, hSum2, hs2Eq, hSum1, hs1Eq]
        rfl

private theorem honestSponge3Perm3_sum (c0 c1 c2 : VcLane6_3) (sc : Fin 3 → Sponge3Coins) :
    vcSumLane6_3 (honestSponge3Perm3 c0 c1 c2 sc).2 =
      state12Rate6 (absorbRate6Sponge3 (vcSumLane6_3 c0) (vcSumLane6_3 c1) (vcSumLane6_3 c2)) := by
  have h0 := pairCheckSponge3Perm_honest c0 c1 c2 sc 0
  have h1 := pairCheckSponge3Perm_honest c0 c1 c2 sc 1
  have h2 := pairCheckSponge3Perm_honest c0 c1 c2 sc 2
  obtain ⟨out6, e0, e1, _, hSum⟩ := pairCheckSponge3Perm_extract3 h0 h1 h2
  have hEq : (honestSponge3Perm3 c0 c1 c2 sc).2 = out6 := by
    apply funext
    refine fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1)
  rwa [hEq]

/-- Single party's view for one 6-limb Merkle accumulator level (`blind_vc.rs:1993-2038`). -/
structure PartyMerkleLevelView where
  bitShare : Goldilocks
  sibShare : Lane6
  boolGate : PartyMulView
  sel0 : PartyMulView
  sel1 : PartyMulView
  sel2 : PartyMulView
  sel3 : PartyMulView
  sel4 : PartyMulView
  sel5 : PartyMulView
  hashView : PartySponge3PermView
  deriving DecidableEq, Repr

def extractMerkleLevelCoins (lv : PartyMerkleLevelView) : Option MerkleLevelCoins :=
  (extractSponge3Coins lv.hashView).map (fun hc =>
    ⟨lv.boolGate.r, lv.sel0.r, lv.sel1.r, lv.sel2.r, lv.sel3.r, lv.sel4.r, lv.sel5.r, hc⟩)

def pairSubGold (a b : Goldilocks × Goldilocks) : Goldilocks × Goldilocks :=
  (Goldilocks.sub a.1 b.1, Goldilocks.sub a.2 b.2)

def pairAddGold (a b : Goldilocks × Goldilocks) : Goldilocks × Goldilocks :=
  (Goldilocks.add a.1 b.1, Goldilocks.add a.2 b.2)

/-- Verify one 6-limb Merkle level at challenge `e`, returning `(nextCurNodePair, boolZeroPair)`. -/
def pairCheckMerkleLevel (e : Fin 3) (epoch : UInt64) (layer : Nat)
    (cur : Lane6 × Lane6) (lvE lvE1 : PartyMerkleLevelView) :
    Option ((Lane6 × Lane6) × (Goldilocks × Goldilocks)) :=
  let b := (lvE.bitShare, lvE1.bitShare)
  let oneWire := vcConstPair e Goldilocks.one
  let oneMinusB := pairSubGold oneWire b
  match pairCheckMul b oneMinusB lvE.boolGate lvE1.boolGate with
  | none => none
  | some boolZero =>
    let d0 := pairSubGold (lvE.sibShare.x0, lvE1.sibShare.x0) (cur.1.x0, cur.2.x0)
    let d1 := pairSubGold (lvE.sibShare.x1, lvE1.sibShare.x1) (cur.1.x1, cur.2.x1)
    let d2 := pairSubGold (lvE.sibShare.x2, lvE1.sibShare.x2) (cur.1.x2, cur.2.x2)
    let d3 := pairSubGold (lvE.sibShare.x3, lvE1.sibShare.x3) (cur.1.x3, cur.2.x3)
    let d4 := pairSubGold (lvE.sibShare.x4, lvE1.sibShare.x4) (cur.1.x4, cur.2.x4)
    let d5 := pairSubGold (lvE.sibShare.x5, lvE1.sibShare.x5) (cur.1.x5, cur.2.x5)
    match pairCheckMul b d0 lvE.sel0 lvE1.sel0,
          pairCheckMul b d1 lvE.sel1 lvE1.sel1,
          pairCheckMul b d2 lvE.sel2 lvE1.sel2,
          pairCheckMul b d3 lvE.sel3 lvE1.sel3,
          pairCheckMul b d4 lvE.sel4 lvE1.sel4,
          pairCheckMul b d5 lvE.sel5 lvE1.sel5 with
    | some del0, some del1, some del2, some del3, some del4, some del5 =>
      let l0 := pairAddGold (cur.1.x0, cur.2.x0) del0
      let l1 := pairAddGold (cur.1.x1, cur.2.x1) del1
      let l2 := pairAddGold (cur.1.x2, cur.2.x2) del2
      let l3 := pairAddGold (cur.1.x3, cur.2.x3) del3
      let l4 := pairAddGold (cur.1.x4, cur.2.x4) del4
      let l5 := pairAddGold (cur.1.x5, cur.2.x5) del5
      let r0 := pairSubGold (lvE.sibShare.x0, lvE1.sibShare.x0) del0
      let r1 := pairSubGold (lvE.sibShare.x1, lvE1.sibShare.x1) del1
      let r2 := pairSubGold (lvE.sibShare.x2, lvE1.sibShare.x2) del2
      let r3 := pairSubGold (lvE.sibShare.x3, lvE1.sibShare.x3) del3
      let r4 := pairSubGold (lvE.sibShare.x4, lvE1.sibShare.x4) del4
      let r5 := pairSubGold (lvE.sibShare.x5, lvE1.sibShare.x5) del5
      let k0 := vcConstPair e (vcSchemaLo epoch)
      let k1 := vcConstPair e (Goldilocks.ofNat layer)
      let k2 := vcConstPair e (Goldilocks.ofNat vcMerkleNodeTag.toNat)
      let k3 := vcConstPair e (vcSchemaHiWithTag epoch poseidon2ConstIV)
      let k4 := vcConstPair e Goldilocks.one
      let c0Pair : Lane6 × Lane6 := (⟨l0.1, l1.1, l2.1, l3.1, l4.1, l5.1⟩, ⟨l0.2, l1.2, l2.2, l3.2, l4.2, l5.2⟩)
      let c1Pair : Lane6 × Lane6 := (⟨r0.1, r1.1, r2.1, r3.1, r4.1, r5.1⟩, ⟨r0.2, r1.2, r2.2, r3.2, r4.2, r5.2⟩)
      let c2Pair : Lane6 × Lane6 :=
        (⟨k0.1, k1.1, k2.1, k3.1, k4.1, Goldilocks.zero⟩,
         ⟨k0.2, k1.2, k2.2, k3.2, k4.2, Goldilocks.zero⟩)
      match pairCheckSponge3Perm e lvE.hashView lvE1.hashView c0Pair c1Pair c2Pair with
      | none => none
      | some nextPair => some (nextPair, boolZero)
    | _, _, _, _, _, _ => none

def honestMerkleLevel3 (epoch : UInt64) (layer : Nat) (cur : VcLane6_3)
    (b : VcWire3) (sib : VcLane6_3) (mc : Fin 3 → MerkleLevelCoins) :
    (Fin 3 → PartyMerkleLevelView) × VcLane6_3 × VcWire3 :=
  let oneMinusB : VcWire3 := fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (b i)
  let bg := honestMulView3 b oneMinusB (fun i => (mc i).boolR)
  let bz := vcMulGate3 b oneMinusB (fun i => (mc i).boolR)
  let d0 : VcWire3 := fun i => Goldilocks.sub (sib i).x0 (cur i).x0
  let d1 : VcWire3 := fun i => Goldilocks.sub (sib i).x1 (cur i).x1
  let d2 : VcWire3 := fun i => Goldilocks.sub (sib i).x2 (cur i).x2
  let d3 : VcWire3 := fun i => Goldilocks.sub (sib i).x3 (cur i).x3
  let d4 : VcWire3 := fun i => Goldilocks.sub (sib i).x4 (cur i).x4
  let d5 : VcWire3 := fun i => Goldilocks.sub (sib i).x5 (cur i).x5
  let s0 := honestMulView3 b d0 (fun i => (mc i).sel0R); let del0 := vcMulGate3 b d0 (fun i => (mc i).sel0R)
  let s1 := honestMulView3 b d1 (fun i => (mc i).sel1R); let del1 := vcMulGate3 b d1 (fun i => (mc i).sel1R)
  let s2 := honestMulView3 b d2 (fun i => (mc i).sel2R); let del2 := vcMulGate3 b d2 (fun i => (mc i).sel2R)
  let s3 := honestMulView3 b d3 (fun i => (mc i).sel3R); let del3 := vcMulGate3 b d3 (fun i => (mc i).sel3R)
  let s4 := honestMulView3 b d4 (fun i => (mc i).sel4R); let del4 := vcMulGate3 b d4 (fun i => (mc i).sel4R)
  let s5 := honestMulView3 b d5 (fun i => (mc i).sel5R); let del5 := vcMulGate3 b d5 (fun i => (mc i).sel5R)
  let c0 : VcLane6_3 := fun i =>
    ⟨Goldilocks.add (cur i).x0 (del0 i), Goldilocks.add (cur i).x1 (del1 i),
     Goldilocks.add (cur i).x2 (del2 i), Goldilocks.add (cur i).x3 (del3 i),
     Goldilocks.add (cur i).x4 (del4 i), Goldilocks.add (cur i).x5 (del5 i)⟩
  let c1 : VcLane6_3 := fun i =>
    ⟨Goldilocks.sub (sib i).x0 (del0 i), Goldilocks.sub (sib i).x1 (del1 i),
     Goldilocks.sub (sib i).x2 (del2 i), Goldilocks.sub (sib i).x3 (del3 i),
     Goldilocks.sub (sib i).x4 (del4 i), Goldilocks.sub (sib i).x5 (del5 i)⟩
  let c2 : VcLane6_3 := fun i =>
    ⟨vcConstWire3 (vcSchemaLo epoch) i,
     vcConstWire3 (Goldilocks.ofNat layer) i,
     vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
     vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
     vcConstWire3 Goldilocks.one i,
     Goldilocks.zero⟩
  let sp := honestSponge3Perm3 c0 c1 c2 (fun i => (mc i).hashCoins)
  (fun i => ⟨b i, sib i, bg i, s0 i, s1 i, s2 i, s3 i, s4 i, s5 i, sp.1 i⟩, sp.2, bz)

private theorem extractMerkleLevelCoins_honest (epoch : UInt64) (layer : Nat) (cur : VcLane6_3)
    (b : VcWire3) (sib : VcLane6_3) (mc : Fin 3 → MerkleLevelCoins) (i : Fin 3) :
    extractMerkleLevelCoins ((honestMerkleLevel3 epoch layer cur b sib mc).1 i) = some (mc i) := by
  unfold extractMerkleLevelCoins honestMerkleLevel3 honestMulView3
  dsimp only
  simp only [extractSponge3Coins_honest, Option.map]

private theorem pairCheckMerkleLevel_honest (epoch : UInt64) (layer : Nat)
    (cur : VcLane6_3) (b : VcWire3) (sib : VcLane6_3) (mc : Fin 3 → MerkleLevelCoins) (e : Fin 3) :
    pairCheckMerkleLevel e epoch layer (vcPairAtLane6 cur e)
      ((honestMerkleLevel3 epoch layer cur b sib mc).1 e)
      ((honestMerkleLevel3 epoch layer cur b sib mc).1 (vcNextParty3 e)) =
      some (vcPairAtLane6 (honestMerkleLevel3 epoch layer cur b sib mc).2.1 e,
            vcPairAt (honestMerkleLevel3 epoch layer cur b sib mc).2.2 e) := by
  unfold pairCheckMerkleLevel honestMerkleLevel3 vcPairAtLane6
  dsimp only
  rw [vcConstPair_spec Goldilocks.one e,
      vcConstPair_spec (vcSchemaLo epoch) e,
      vcConstPair_spec (Goldilocks.ofNat layer) e,
      vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) e,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) e]
  have hOneSub : pairSubGold (vcPairAt (vcConstWire3 Goldilocks.one) e) (b e, b (vcNextParty3 e)) =
      vcPairAt (fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (b i)) e := rfl
  have hbPair : (b e, b (vcNextParty3 e)) = vcPairAt b e := rfl
  have hd0 : pairSubGold ((sib e).x0, (sib (vcNextParty3 e)).x0) ((cur e).x0, (cur (vcNextParty3 e)).x0) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x0 (cur i).x0) e := rfl
  have hd1 : pairSubGold ((sib e).x1, (sib (vcNextParty3 e)).x1) ((cur e).x1, (cur (vcNextParty3 e)).x1) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x1 (cur i).x1) e := rfl
  have hd2 : pairSubGold ((sib e).x2, (sib (vcNextParty3 e)).x2) ((cur e).x2, (cur (vcNextParty3 e)).x2) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x2 (cur i).x2) e := rfl
  have hd3 : pairSubGold ((sib e).x3, (sib (vcNextParty3 e)).x3) ((cur e).x3, (cur (vcNextParty3 e)).x3) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x3 (cur i).x3) e := rfl
  have hd4 : pairSubGold ((sib e).x4, (sib (vcNextParty3 e)).x4) ((cur e).x4, (cur (vcNextParty3 e)).x4) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x4 (cur i).x4) e := rfl
  have hd5 : pairSubGold ((sib e).x5, (sib (vcNextParty3 e)).x5) ((cur e).x5, (cur (vcNextParty3 e)).x5) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x5 (cur i).x5) e := rfl
  rw [hOneSub, hbPair, pairCheckMul_honest, hd0, hd1, hd2, hd3, hd4, hd5,
      pairCheckMul_honest, pairCheckMul_honest, pairCheckMul_honest,
      pairCheckMul_honest, pairCheckMul_honest, pairCheckMul_honest]
  dsimp only
  have hsp := pairCheckSponge3Perm_honest
    (fun i =>
      ⟨Goldilocks.add (cur i).x0 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x0 (cur k).x0) (fun k => (mc k).sel0R) i),
       Goldilocks.add (cur i).x1 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x1 (cur k).x1) (fun k => (mc k).sel1R) i),
       Goldilocks.add (cur i).x2 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x2 (cur k).x2) (fun k => (mc k).sel2R) i),
       Goldilocks.add (cur i).x3 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x3 (cur k).x3) (fun k => (mc k).sel3R) i),
       Goldilocks.add (cur i).x4 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x4 (cur k).x4) (fun k => (mc k).sel4R) i),
       Goldilocks.add (cur i).x5 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x5 (cur k).x5) (fun k => (mc k).sel5R) i)⟩)
    (fun i =>
      ⟨Goldilocks.sub (sib i).x0 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x0 (cur k).x0) (fun k => (mc k).sel0R) i),
       Goldilocks.sub (sib i).x1 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x1 (cur k).x1) (fun k => (mc k).sel1R) i),
       Goldilocks.sub (sib i).x2 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x2 (cur k).x2) (fun k => (mc k).sel2R) i),
       Goldilocks.sub (sib i).x3 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x3 (cur k).x3) (fun k => (mc k).sel3R) i),
       Goldilocks.sub (sib i).x4 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x4 (cur k).x4) (fun k => (mc k).sel4R) i),
       Goldilocks.sub (sib i).x5 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x5 (cur k).x5) (fun k => (mc k).sel5R) i)⟩)
    (fun i =>
      ⟨vcConstWire3 (vcSchemaLo epoch) i,
       vcConstWire3 (Goldilocks.ofNat layer) i,
       vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
       vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
       vcConstWire3 Goldilocks.one i,
       Goldilocks.zero⟩)
    (fun i => (mc i).hashCoins) e
  dsimp only [vcPairAtLane6, pairAddGold, pairSubGold, vcPairAt] at hsp ⊢
  rw [hsp]

private theorem pairCheckMerkleLevel_extract3 {epoch : UInt64} {layer : Nat}
    {cur : VcLane6_3} {lv : Fin 3 → PartyMerkleLevelView}
    {o0 o1 o2 : (Lane6 × Lane6) × (Goldilocks × Goldilocks)}
    (h0 : pairCheckMerkleLevel 0 epoch layer (vcPairAtLane6 cur 0) (lv 0) (lv 1) = some o0)
    (h1 : pairCheckMerkleLevel 1 epoch layer (vcPairAtLane6 cur 1) (lv 1) (lv 2) = some o1)
    (h2 : pairCheckMerkleLevel 2 epoch layer (vcPairAtLane6 cur 2) (lv 2) (lv 0) = some o2) :
    ∃ (nextCur : VcLane6_3) (bz : VcWire3),
      o0 = (vcPairAtLane6 nextCur 0, vcPairAt bz 0) ∧
      o1 = (vcPairAtLane6 nextCur 1, vcPairAt bz 1) ∧
      o2 = (vcPairAtLane6 nextCur 2, vcPairAt bz 2) ∧
      vcSum3 bz = Goldilocks.mul (vcSum3 (fun i => (lv i).bitShare))
        (Goldilocks.sub Goldilocks.one (vcSum3 (fun i => (lv i).bitShare))) ∧
      vcSumLane6_3 nextCur =
        vcMerkleStepArith epoch layer (vcSumLane6_3 cur)
          (vcSumLane6_3 (fun i => (lv i).sibShare)) (vcSum3 (fun i => (lv i).bitShare)) := by
  unfold pairCheckMerkleLevel at h0 h1 h2
  rw [vcConstPair_spec Goldilocks.one 0, vcConstPair_spec (vcSchemaLo epoch) 0,
      vcConstPair_spec (Goldilocks.ofNat layer) 0, vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) 0,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) 0] at h0
  rw [vcConstPair_spec Goldilocks.one 1, vcConstPair_spec (vcSchemaLo epoch) 1,
      vcConstPair_spec (Goldilocks.ofNat layer) 1, vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) 1,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) 1] at h1
  rw [vcConstPair_spec Goldilocks.one 2, vcConstPair_spec (vcSchemaLo epoch) 2,
      vcConstPair_spec (Goldilocks.ofNat layer) 2, vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) 2,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) 2] at h2
  let bw : VcWire3 := fun i => (lv i).bitShare
  let omb : VcWire3 := fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (bw i)
  dsimp only [vcPairAtLane6, vcPairAt, vcNextParty3, pairSubGold, pairAddGold] at h0 h1 h2
  cases hb0 : pairCheckMul (vcPairAt bw 0) (vcPairAt omb 0) (lv 0).boolGate (lv 1).boolGate with
  | none => have hb0' := hb0; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb0'; rw [hb0'] at h0; cases h0
  | some bz0 =>
  cases hb1 : pairCheckMul (vcPairAt bw 1) (vcPairAt omb 1) (lv 1).boolGate (lv 2).boolGate with
  | none => have hb1' := hb1; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb1'; rw [hb1'] at h1; cases h1
  | some bz1 =>
  cases hb2 : pairCheckMul (vcPairAt bw 2) (vcPairAt omb 2) (lv 2).boolGate (lv 0).boolGate with
  | none => have hb2' := hb2; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb2'; rw [hb2'] at h2; cases h2
  | some bz2 =>
    have hb0' := hb0; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb0'
    have hb1' := hb1; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb1'
    have hb2' := hb2; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb2'
    rw [hb0'] at h0; rw [hb1'] at h1; rw [hb2'] at h2
    dsimp only at h0 h1 h2
    let dw0 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x0 (cur i).x0
    let dw1 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x1 (cur i).x1
    let dw2 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x2 (cur i).x2
    let dw3 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x3 (cur i).x3
    let dw4 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x4 (cur i).x4
    let dw5 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x5 (cur i).x5
    cases s00 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw0 0) (lv 0).sel0 (lv 1).sel0 with
    | none => have u := s00; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u00 := s00; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u00; rw [u00] at h0
    cases s10 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw1 0) (lv 0).sel1 (lv 1).sel1 with
    | none => have u := s10; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u10 := s10; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u10; rw [u10] at h0
    cases s20 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw2 0) (lv 0).sel2 (lv 1).sel2 with
    | none => have u := s20; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u20 := s20; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u20; rw [u20] at h0
    cases s30 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw3 0) (lv 0).sel3 (lv 1).sel3 with
    | none => have u := s30; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u30 := s30; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u30; rw [u30] at h0
    cases s40 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw4 0) (lv 0).sel4 (lv 1).sel4 with
    | none => have u := s40; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u40 := s40; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u40; rw [u40] at h0
    cases s50 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw5 0) (lv 0).sel5 (lv 1).sel5 with
    | none => have u := s50; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u50 := s50; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u50; rw [u50] at h0
    cases s01 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw0 1) (lv 1).sel0 (lv 2).sel0 with
    | none => have u := s01; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u01 := s01; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u01; rw [u01] at h1
    cases s11 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw1 1) (lv 1).sel1 (lv 2).sel1 with
    | none => have u := s11; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u11 := s11; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u11; rw [u11] at h1
    cases s21 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw2 1) (lv 1).sel2 (lv 2).sel2 with
    | none => have u := s21; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u21 := s21; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u21; rw [u21] at h1
    cases s31 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw3 1) (lv 1).sel3 (lv 2).sel3 with
    | none => have u := s31; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u31 := s31; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u31; rw [u31] at h1
    cases s41 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw4 1) (lv 1).sel4 (lv 2).sel4 with
    | none => have u := s41; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u41 := s41; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u41; rw [u41] at h1
    cases s51 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw5 1) (lv 1).sel5 (lv 2).sel5 with
    | none => have u := s51; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u51 := s51; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u51; rw [u51] at h1
    cases s02 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw0 2) (lv 2).sel0 (lv 0).sel0 with
    | none => have u := s02; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u02 := s02; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u02; rw [u02] at h2
    cases s12 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw1 2) (lv 2).sel1 (lv 0).sel1 with
    | none => have u := s12; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u12 := s12; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u12; rw [u12] at h2
    cases s22 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw2 2) (lv 2).sel2 (lv 0).sel2 with
    | none => have u := s22; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u22 := s22; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u22; rw [u22] at h2
    cases s32 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw3 2) (lv 2).sel3 (lv 0).sel3 with
    | none => have u := s32; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u32 := s32; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u32; rw [u32] at h2
    cases s42 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw4 2) (lv 2).sel4 (lv 0).sel4 with
    | none => have u := s42; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u42 := s42; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u42; rw [u42] at h2
    cases s52 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw5 2) (lv 2).sel5 (lv 0).sel5 with
    | none => have u := s52; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
      have u52 := s52; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u52; rw [u52] at h2
      dsimp only at h0 h1 h2
      rw [(pairCheckMul_step (g := fun i => (lv i).boolGate) (e := 0) hb0).1] at h0
      rw [(pairCheckMul_step (g := fun i => (lv i).boolGate) (e := 1) hb1).1] at h1
      rw [(pairCheckMul_step (g := fun i => (lv i).boolGate) (e := 2) hb2).1] at h2
      rw [(pairCheckMul_step (g := fun i => (lv i).sel0) (e := 0) s00).1,
          (pairCheckMul_step (g := fun i => (lv i).sel1) (e := 0) s10).1,
          (pairCheckMul_step (g := fun i => (lv i).sel2) (e := 0) s20).1,
          (pairCheckMul_step (g := fun i => (lv i).sel3) (e := 0) s30).1,
          (pairCheckMul_step (g := fun i => (lv i).sel4) (e := 0) s40).1,
          (pairCheckMul_step (g := fun i => (lv i).sel5) (e := 0) s50).1] at h0
      rw [(pairCheckMul_step (g := fun i => (lv i).sel0) (e := 1) s01).1,
          (pairCheckMul_step (g := fun i => (lv i).sel1) (e := 1) s11).1,
          (pairCheckMul_step (g := fun i => (lv i).sel2) (e := 1) s21).1,
          (pairCheckMul_step (g := fun i => (lv i).sel3) (e := 1) s31).1,
          (pairCheckMul_step (g := fun i => (lv i).sel4) (e := 1) s41).1,
          (pairCheckMul_step (g := fun i => (lv i).sel5) (e := 1) s51).1] at h1
      rw [(pairCheckMul_step (g := fun i => (lv i).sel0) (e := 2) s02).1,
          (pairCheckMul_step (g := fun i => (lv i).sel1) (e := 2) s12).1,
          (pairCheckMul_step (g := fun i => (lv i).sel2) (e := 2) s22).1,
          (pairCheckMul_step (g := fun i => (lv i).sel3) (e := 2) s32).1,
          (pairCheckMul_step (g := fun i => (lv i).sel4) (e := 2) s42).1,
          (pairCheckMul_step (g := fun i => (lv i).sel5) (e := 2) s52).1] at h2
      dsimp only [vcPairAt, vcNextParty3] at h0 h1 h2
      let c0_3 : VcLane6_3 := fun i =>
        ⟨Goldilocks.add (cur i).x0 (lv i).sel0.out, Goldilocks.add (cur i).x1 (lv i).sel1.out,
         Goldilocks.add (cur i).x2 (lv i).sel2.out, Goldilocks.add (cur i).x3 (lv i).sel3.out,
         Goldilocks.add (cur i).x4 (lv i).sel4.out, Goldilocks.add (cur i).x5 (lv i).sel5.out⟩
      let c1_3 : VcLane6_3 := fun i =>
        ⟨Goldilocks.sub (lv i).sibShare.x0 (lv i).sel0.out, Goldilocks.sub (lv i).sibShare.x1 (lv i).sel1.out,
         Goldilocks.sub (lv i).sibShare.x2 (lv i).sel2.out, Goldilocks.sub (lv i).sibShare.x3 (lv i).sel3.out,
         Goldilocks.sub (lv i).sibShare.x4 (lv i).sel4.out, Goldilocks.sub (lv i).sibShare.x5 (lv i).sel5.out⟩
      let c2_3 : VcLane6_3 := fun i =>
        ⟨vcConstWire3 (vcSchemaLo epoch) i,
         vcConstWire3 (Goldilocks.ofNat layer) i,
         vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
         vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
         vcConstWire3 Goldilocks.one i,
         Goldilocks.zero⟩
      cases sp0 : pairCheckSponge3Perm 0 (lv 0).hashView (lv 1).hashView
          (vcPairAtLane6 c0_3 0) (vcPairAtLane6 c1_3 0) (vcPairAtLane6 c2_3 0) with
      | none => have sp0' := sp0; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp0'; rw [sp0'] at h0; cases h0
      | some u0 =>
      cases sp1 : pairCheckSponge3Perm 1 (lv 1).hashView (lv 2).hashView
          (vcPairAtLane6 c0_3 1) (vcPairAtLane6 c1_3 1) (vcPairAtLane6 c2_3 1) with
      | none => have sp1' := sp1; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp1'; rw [sp1'] at h1; cases h1
      | some u1 =>
      cases sp2 : pairCheckSponge3Perm 2 (lv 2).hashView (lv 0).hashView
          (vcPairAtLane6 c0_3 2) (vcPairAtLane6 c1_3 2) (vcPairAtLane6 c2_3 2) with
      | none => have sp2' := sp2; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp2'; rw [sp2'] at h2; cases h2
      | some u2 =>
        have sp0' := sp0; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp0'
        have sp1' := sp1; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp1'
        have sp2' := sp2; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp2'
        rw [sp0'] at h0; rw [sp1'] at h1; rw [sp2'] at h2
        dsimp only at h0 h1 h2
        obtain ⟨nextCur, hu0, hu1, hu2, hSpSum⟩ :=
          pairCheckSponge3Perm_extract3 (sv := fun i => (lv i).hashView) sp0 sp1 sp2
        rw [hu0] at h0; rw [hu1] at h1; rw [hu2] at h2
        injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
        refine ⟨nextCur, fun i => (lv i).boolGate.out, ho0.symm, ho1.symm, ho2.symm, ?_, ?_⟩
        · have hBz := pairCheckMul_extract3 (g := fun i => (lv i).boolGate) hb0 hb1 hb2
          rw [hBz]; congr 1; dsimp only [omb]; rw [vcSum3_sub, vcSum3_constWire]
        · rw [hSpSum]
          unfold vcMerkleStepArith vcMerkleHashPair vcMerkleChunks lane6Add lane6Sub lane6Scale
          dsimp only
          congr 1
          simp only [vcSumLane6_3_eq]
          dsimp only [c0_3, c1_3, c2_3]
          simp only [vcSum3_add, vcSum3_sub, vcSum3_constWire, vcSum3_zero]
          rw [pairCheckMul_extract3 (g := fun i => (lv i).sel0) s00 s01 s02,
              pairCheckMul_extract3 (g := fun i => (lv i).sel1) s10 s11 s12,
              pairCheckMul_extract3 (g := fun i => (lv i).sel2) s20 s21 s22,
              pairCheckMul_extract3 (g := fun i => (lv i).sel3) s30 s31 s32,
              pairCheckMul_extract3 (g := fun i => (lv i).sel4) s40 s41 s42,
              pairCheckMul_extract3 (g := fun i => (lv i).sel5) s50 s51 s52]
          dsimp only [bw, dw0, dw1, dw2, dw3, dw4, dw5]
          simp only [vcSum3_sub]

def pairCheckMerklePath (e : Fin 3) (epoch : UInt64) :
    Nat → (Lane6 × Lane6) → List PartyMerkleLevelView → List PartyMerkleLevelView →
    Option ((Lane6 × Lane6) × List (Goldilocks × Goldilocks))
  | _, cur, [], [] => some (cur, [])
  | layer, cur, lvE :: restE, lvE1 :: restE1 =>
    match pairCheckMerkleLevel e epoch layer cur lvE lvE1 with
    | none => none
    | some (nextCur, bz) =>
      match pairCheckMerklePath e epoch (layer + 1) nextCur restE restE1 with
      | none => none
      | some (rootPair, bzs) => some (rootPair, bz :: bzs)
  | _, _, _, _ => none

def extractMerklePathCoins : (D : Nat) → List PartyMerkleLevelView → Option (Vec MerkleLevelCoins D)
  | 0, [] => some .nil
  | d + 1, lv :: rest =>
    match extractMerkleLevelCoins lv, extractMerklePathCoins d rest with
    | some hc, some tc => some (.cons hc tc)
    | _, _ => none
  | _, _ => none

def honestMerklePath3 (epoch : UInt64) :
    {D : Nat} → Nat → VcLane6_3 → Vec (VcWire3 × VcLane6_3) D → (Fin 3 → Vec MerkleLevelCoins D) →
    (Fin 3 → List PartyMerkleLevelView) × VcLane6_3 × List VcWire3
  | 0, _, cur, .nil, _ => (fun _ => [], cur, [])
  | _ + 1, layer, cur, .cons (b, sib) rest, mcs =>
    let step := honestMerkleLevel3 epoch layer cur b sib (fun i => (mcs i).head)
    let tail := honestMerklePath3 epoch (layer + 1) step.2.1 rest (fun i => (mcs i).tail)
    (fun i => step.1 i :: tail.1 i, tail.2.1, step.2.2 :: tail.2.2)

private theorem honestMerklePath3_length (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : VcLane6_3) (steps : Vec (VcWire3 × VcLane6_3) D)
      (mcs : Fin 3 → Vec MerkleLevelCoins D) (i : Fin 3),
      ((honestMerklePath3 epoch layer cur steps mcs).1 i).length = D
  | 0, _, _, .nil, _, _ => rfl
  | _ + 1, layer, cur, .cons (_, _) rest, mcs, i => by
    simp only [honestMerklePath3, List.length_cons]
    rw [honestMerklePath3_length epoch (layer + 1) _ rest (fun j => (mcs j).tail) i]

private theorem extractMerklePathCoins_honest (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : VcLane6_3) (steps : Vec (VcWire3 × VcLane6_3) D)
      (mcs : Fin 3 → Vec MerkleLevelCoins D) (i : Fin 3),
      extractMerklePathCoins D ((honestMerklePath3 epoch layer cur steps mcs).1 i) = some (mcs i)
  | 0, _, _, .nil, mcs, i => by cases mcs i; rfl
  | _ + 1, layer, cur, .cons (b, sib) rest, mcs, i => by
    simp only [honestMerklePath3, extractMerklePathCoins]
    rw [extractMerkleLevelCoins_honest,
        extractMerklePathCoins_honest epoch (layer + 1) _ rest (fun j => (mcs j).tail) i]
    dsimp only
    rw [Vec.eta_cons]

private theorem pairCheckMerklePath_honest (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : VcLane6_3) (steps : Vec (VcWire3 × VcLane6_3) D)
      (mcs : Fin 3 → Vec MerkleLevelCoins D) (e : Fin 3),
      pairCheckMerklePath e epoch layer (vcPairAtLane6 cur e)
        ((honestMerklePath3 epoch layer cur steps mcs).1 e)
        ((honestMerklePath3 epoch layer cur steps mcs).1 (vcNextParty3 e)) =
        some (vcPairAtLane6 (honestMerklePath3 epoch layer cur steps mcs).2.1 e,
              (honestMerklePath3 epoch layer cur steps mcs).2.2.map (fun w => vcPairAt w e))
  | 0, _, _, .nil, _, _ => rfl
  | _ + 1, layer, cur, .cons (b, sib) rest, mcs, e => by
    simp only [honestMerklePath3, pairCheckMerklePath, List.map]
    rw [pairCheckMerkleLevel_honest]; dsimp only
    rw [pairCheckMerklePath_honest epoch (layer + 1) _ rest (fun i => (mcs i).tail) e]

private theorem pairCheckMerklePath_extract3 (epoch : UInt64) :
    ∀ (depth layer : Nat) (cur : VcLane6_3) (lvs : Fin 3 → List PartyMerkleLevelView)
      {o0 o1 o2 : (Lane6 × Lane6) × List (Goldilocks × Goldilocks)},
      (lvs 0).length = depth →
      pairCheckMerklePath 0 epoch layer (vcPairAtLane6 cur 0) (lvs 0) (lvs 1) = some o0 →
      pairCheckMerklePath 1 epoch layer (vcPairAtLane6 cur 1) (lvs 1) (lvs 2) = some o1 →
      pairCheckMerklePath 2 epoch layer (vcPairAtLane6 cur 2) (lvs 2) (lvs 0) = some o2 →
      ∃ (root3 : VcLane6_3) (bzs3 : List VcWire3) (steps : List (Goldilocks × Lane6)),
        steps.length = depth ∧
        o0 = (vcPairAtLane6 root3 0, bzs3.map (fun w => vcPairAt w 0)) ∧
        o1 = (vcPairAtLane6 root3 1, bzs3.map (fun w => vcPairAt w 1)) ∧
        o2 = (vcPairAtLane6 root3 2, bzs3.map (fun w => vcPairAt w 2)) ∧
        ((∀ z ∈ bzs3, vcSum3 z = Goldilocks.zero) →
          ∀ p ∈ steps, p.1 = Goldilocks.zero ∨ p.1 = Goldilocks.one) ∧
        vcSumLane6_3 root3 = evalVcMerklePathFrom epoch layer (vcSumLane6_3 cur) steps
  | 0, layer, cur, lvs, o0, o1, o2, hLen0, h0, h1, h2 => by
    cases hv0 : lvs 0 with
    | cons _ _ => rw [hv0] at hLen0; cases hLen0
    | nil =>
      cases hv1 : lvs 1 with
      | cons _ _ => rw [hv0, hv1] at h0; cases h0
      | nil =>
        cases hv2 : lvs 2 with
        | cons _ _ => rw [hv1, hv2] at h1; cases h1
        | nil =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckMerklePath] at h0 h1 h2
          injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
          exact ⟨cur, [], [], rfl, ho0.symm, ho1.symm, ho2.symm, (fun _ _ hp => nomatch hp), rfl⟩
  | depth + 1, layer, cur, lvs, o0, o1, o2, hLen0, h0, h1, h2 => by
    cases hv0 : lvs 0 with
    | nil => rw [hv0] at hLen0; cases hLen0
    | cons r0 rs0 =>
      rw [hv0] at hLen0; simp only [List.length_cons] at hLen0
      cases hv1 : lvs 1 with
      | nil => rw [hv0, hv1] at h0; cases h0
      | cons r1 rs1 =>
        cases hv2 : lvs 2 with
        | nil => rw [hv1, hv2] at h1; cases h1
        | cons r2 rs2 =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckMerklePath] at h0 h1 h2
          let lv : Fin 3 → PartyMerkleLevelView := fun | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2
          let rs : Fin 3 → List PartyMerkleLevelView := fun | ⟨0, _⟩ => rs0 | ⟨1, _⟩ => rs1 | ⟨2, _⟩ => rs2
          cases m0 : pairCheckMerkleLevel 0 epoch layer (vcPairAtLane6 cur 0) (lv 0) (lv 1) with
          | none => have m0' := m0; dsimp only [lv] at m0'; rw [m0'] at h0; cases h0
          | some p0 =>
          cases m1 : pairCheckMerkleLevel 1 epoch layer (vcPairAtLane6 cur 1) (lv 1) (lv 2) with
          | none => have m1' := m1; dsimp only [lv] at m1'; rw [m1'] at h1; cases h1
          | some p1 =>
          cases m2 : pairCheckMerkleLevel 2 epoch layer (vcPairAtLane6 cur 2) (lv 2) (lv 0) with
          | none => have m2' := m2; dsimp only [lv] at m2'; rw [m2'] at h2; cases h2
          | some p2 =>
            have m0' := m0; dsimp only [lv] at m0'
            have m1' := m1; dsimp only [lv] at m1'
            have m2' := m2; dsimp only [lv] at m2'
            rw [m0'] at h0; rw [m1'] at h1; rw [m2'] at h2
            obtain ⟨nextCur, bz, ep0, ep1, ep2, hBzEq, hNextEq⟩ := pairCheckMerkleLevel_extract3 m0 m1 m2
            rw [ep0] at h0; rw [ep1] at h1; rw [ep2] at h2
            dsimp only at h0 h1 h2
            cases t0 : pairCheckMerklePath 0 epoch (layer + 1) (vcPairAtLane6 nextCur 0) (rs 0) (rs 1) with
            | none => have t0' := t0; dsimp only [rs] at t0'; rw [t0'] at h0; cases h0
            | some q0 =>
            cases t1 : pairCheckMerklePath 1 epoch (layer + 1) (vcPairAtLane6 nextCur 1) (rs 1) (rs 2) with
            | none => have t1' := t1; dsimp only [rs] at t1'; rw [t1'] at h1; cases h1
            | some q1 =>
            cases t2 : pairCheckMerklePath 2 epoch (layer + 1) (vcPairAtLane6 nextCur 2) (rs 2) (rs 0) with
            | none => have t2' := t2; dsimp only [rs] at t2'; rw [t2'] at h2; cases h2
            | some q2 =>
              have t0' := t0; dsimp only [rs] at t0'
              have t1' := t1; dsimp only [rs] at t1'
              have t2' := t2; dsimp only [rs] at t2'
              rw [t0'] at h0; rw [t1'] at h1; rw [t2'] at h2
              obtain ⟨root3, bzs3, stepsRest, hSLen, eq0, eq1, eq2, hBoolRest, hRootSum⟩ :=
                pairCheckMerklePath_extract3 epoch depth (layer + 1) nextCur rs (by dsimp [rs]; omega) t0 t1 t2
              rw [eq0] at h0; rw [eq1] at h1; rw [eq2] at h2
              dsimp only at h0 h1 h2
              injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
              let bVal := vcSum3 (fun i => (lv i).bitShare)
              let sibVal := vcSumLane6_3 (fun i => (lv i).sibShare)
              refine ⟨root3, bz :: bzs3, (bVal, sibVal) :: stepsRest,
                by simp [hSLen], ho0.symm, ho1.symm, ho2.symm, ?_, ?_⟩
              · intro hAllZ p hp
                rcases List.mem_cons.mp hp with rfl | hpRest
                · have h0Bz : vcSum3 bz = Goldilocks.zero := hAllZ bz (.head bzs3)
                  rw [hBzEq] at h0Bz
                  exact goldilocks_bool_gate_zero_or_one bVal h0Bz
                · exact hBoolRest (fun z hz => hAllZ z (.tail bz hz)) p hpRest
              · dsimp only [evalVcMerklePathFrom]
                rw [← hNextEq]
                exact hRootSum


/-! ### §4.4 Round-1 View Commitments, PRG Tape Replay, Strict Ascending `Nodup`, Fiat-Shamir & 3-Challenge Extraction -/

/-- Concrete 3-party tuple (`DecidableEq`-friendly carrier isomorphic to `Fin 3 → α`). -/
structure Triple3 (α : Type) where
  s0 : α
  s1 : α
  s2 : α
  deriving DecidableEq, Repr

def Triple3.get {α : Type} (t : Triple3 α) : Fin 3 → α
  | ⟨0, _⟩ => t.s0
  | ⟨1, _⟩ => t.s1
  | ⟨2, _⟩ => t.s2

def Triple3.ofFn {α : Type} (f : Fin 3 → α) : Triple3 α :=
  ⟨f 0, f 1, f 2⟩

private theorem Triple3.get_ofFn {α : Type} (f : Fin 3 → α) (i : Fin 3) :
    (Triple3.ofFn f).get i = f i := by
  rcases i with ⟨iv, hiv⟩
  have hc : iv = 0 ∨ iv = 1 ∨ iv = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rfl

private theorem Triple3.ofFn_get {α : Type} (t : Triple3 α) :
    Triple3.ofFn t.get = t := by
  cases t; rfl

private theorem Triple3.ext_get {α : Type} {a b : Triple3 α}
    (h : ∀ i : Fin 3, a.get i = b.get i) : a = b := by
  cases a; cases b
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  dsimp only [Triple3.get] at h0 h1 h2
  subst h0 h1 h2; rfl

/-- Single party's full ZKBoo repetition view (`blind_vc.rs:258-325, 1805-1905`), carrying
    explicit 32-byte PRG `tapeSeed`, 32-byte broadcast commitment `commitSalt`, secret-shared
    input wires, and all gate transcripts across `attrSponge`, `merkleLevels`, `presSponge`, and `scopeSponge`. -/
structure PartyVcRepView where
  tapeSeed : Vec UInt8 32
  commitSalt : Vec UInt8 32
  attrShares : List Goldilocks
  holderBlindShare : Lane4
  presBlindShare : Lane4
  attrSponge : PartySponge3PermView
  merkleLevels : List PartyMerkleLevelView
  presSponge : PartySponge3PermView
  scopeSponge : PartySponge3PermView
  deriving DecidableEq

/-- Extract the structured gate coin tape embedded inside `v` (`none` if round/path lengths mismatch). -/

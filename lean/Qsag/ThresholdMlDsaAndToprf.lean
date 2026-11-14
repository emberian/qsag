module
/-
# Qsag.ThresholdMlDsaAndToprf — FIPS 204 Threshold ML-DSA-44, 2-of-5 Poseidon2 TOPRF & BlindVC

Complete zero-Mathlib, constructive (`0 Classical.choice`) formalization of the `qsag-cred`
post-quantum threshold signature, oblivious PRF, and selective-disclosure credential suite:

1. **§1. Exact NIST FIPS 204 (`ML-DSA-44`) Field, 256-Point Negacyclic NTT & Rounding Laws:**
   - Constructive primality of $q = 8380417 = 2^{23} - 2^{13} + 1$ (`mldsaQ_isPrime`), canonical
     prime field `Fq204` (`LawfulCommRing`, `NoZeroDivisors`, constructive Bézout inverse
     `Fq204.mul_inv_cancel`), and 64-bit Barrett multiplication equivalence (`fqMulBarrett_sound`).
   - Exact 256-point negacyclic polynomial ring $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$ (`Poly256`),
     8-stage Cooley–Tukey / Gentleman–Sande NTT bijection (`fips204InvNtt_ntt`, `fips204Ntt_invNtt`),
     convolution homomorphism (`fips204Ntt_negacyclicMul`, `fips204InvNtt_pointwiseMul`),
     and transported `LawfulCommRing Poly256` structure on $(R_q, +, \text{negacyclicMul})$.
   - Exact FIPS 204 `power2Round` ($d = 13$), `decompose` / constant-time `decomposeCtSpec`
     ($\alpha = 2\gamma_2 = 190464$), `highBits`, `lowBits`, `makeHint`, `useHint`,
     `power2Round_reconstruct`, `decompose_reconstruct`, centered-difference acceptance equivalence
     (`centered_diff_lt_iff_lowBits_and_highBits`), and the **Exact `HighBits` Shift Lemma**
     (`highBits_az_sub_ct_eq_w1`), paired with `#tooth` boundary-violation counterexamples.

2. **§2. `(t, m)` RSS `F_q[X]/(X^6 - 7)` Threshold ML-DSA-44 DKG & Leakage-Parameterized Signing:**
   - Constructive honest-holder coverage (`subset_honest_holder_exists`, $n \ge 2t - 1$) + `#tooth`
     at $(t=2, n=2)$, pairwise subset intersection for replicated multiplication, and exact 4-bit
     nibble rejection circuit (`dkg_nibble_rejection_circuit_exact`) yielding uniform $[-2, 2]$ shares.
   - Exact `qsag-accel` `cshake256_framed_xof` (`encodeFramesU64Le` + `customizationPrefix`),
     degree-6 extension `Ext6Fq204` ($F_q[X]/(X^6 - 7)$) batch inner-product sacrifice soundness,
     and `"QSAG.TMLDSA.DKG.CONFIRM.V1"` confirmation binding (`dkg_confirm_transcript_binding_and_rss_consistency`)
     + `#tooth` (`tooth_uncommitted_dkg_rogue_key_forgery`).
   - `#tooth` (`premature_z_release_leaks_s2_boundary`) and explicit leakage-parameterized RSS signing
     (`threshold_mldsa_rss_abort_leakage_and_completeness`): rejected attempts emit the exact public abort
     transcript `(openedMaskedW, openedW1, openedMaskedZAndLow, rejectBit := true)` without opening unmasked
     `z`, fresh `< q` RSS masks induce constructive `SimpleEquiv` bijections conditioned on `(w1, rejectBit)`,
     durable `(epoch, sessionId, attempt)` burns advance monotonically across multi-turn traces, and
     accepted attempts satisfy standalone FIPS 204 `mldsaVerify = true`.

3. **§3. Dealerless 2-of-5 Replicated Poseidon2 Threshold OPRF (`voprf.rs` / `toprf_engine.rs`):**
   - Combinatorial $\binom{5}{3} = 10$ subset intersection + exact 5-component `ToprfWire` engine,
     3-holder cross-term resharing over exact `"QSAG.TOPRF.RESHARE.DIGEST.V2"` `cshake256_framed_xof`,
     and 3-of-4 client finalize majority (`toprf_2of5_corrects_one_malicious_server`) + `#tooth` for 2 corrupt servers.
   - Constructive `SimpleEquiv` 1-curious-server input & gate-view privacy (`toprf_one_curious_server_hiding`),
     and `"QSAG.TOPRF.INPUT.COMMIT.V1"` / `"QSAG.TOPRF.INPUT.BIND.V1"` binding including `context.base_digest()`
     (`"QSAG.TOPRF.EVAL.V1"`) (`toprf_input_root_blocks_relabeling_and_equivocation`) + `#tooth`
     (`tooth_omitting_base_digest_allows_cross_session_replay`).

4. **§4. `BlindVC` Rate-6/Capacity-6 6-Limb `sponge12` Commitment & ZKBoo Selective Disclosure:**
   - Explicit-arity (`1 ≤ arity ≤ 6`) 13-limb `vcSponge13` outputting 6-limb `Lane6` (`> 383`-bit)
     commitments (`computeVcPoseidon2Commit`), cross-arity & same-arity binding reduction to `vcSponge13`
     collisions, and `#tooth` (`tooth_unframed_trailing_zero_collision`).
   - Strict ascending `disclosedAttrs` enforcement inside `verifyBlindVcPresentation`, Round-1
     `"QSAG.COMMIT.V1"` party-view commitments + PRG `tapeSeed` replay + Fiat-Shamir challenge derivation,
     3-challenge witness extraction, `ZkSoundnessProfile` (`Quantum128 = 438` `< 2^{-256}` = 128-bit QROM
     Grover challenge-grinding vs `Classical128 = 219` `< 2^{-128}` classical ROM / `< 65`-bit QROM),
     and full `OpenedBlindVcRep` (`PartyVcRepView` pair + `unopenedCommit` + `finalOuts`) `SimpleEquiv` simulation.
-/

public import Qsag.Constructive
public import Qsag.SimulationSpine
public import Qsag.Goldilocks
public import Qsag.Poseidon2
public import Qsag.UcGames
public import Qsag.AdvancedMpcAndCreds

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
def mldsa44Gamma1 : Nat := 131072       -- 2^17
def mldsa44Gamma2 : Nat := 95232        -- (q - 1) / 88
def mldsa44Alpha : Nat := 190464        -- 2 * gamma2 = (q - 1) / 44
def mldsa44HighMod : Nat := 44          -- (q - 1) / alpha
def mldsa44Tau : Nat := 39
def mldsa44Eta : Nat := 2
def mldsa44Beta : Nat := 78             -- tau * eta
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

private theorem nodup_length_le_of_subset :
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
    have ih := nodup_length_le_of_subset (eraseFirstNat x C) hxsNodup hSubTail
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
    {C T : List Nat} (_hCNodup : C.Nodup) (hCLen : C.length ≤ t - 1)
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
      have hLe := nodup_length_le_of_subset C hTNodup hAll
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
    have hLe := nodup_length_le_of_subset (List.range n) hAppNodup hInRange
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
        (if customization = [] then 0x1f else 0x04))) := rfl

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
    `delta ≠ 0` (`rss_mpc.rs:1066-1095`): proves that across all $q^6 = 8380417^6 > 2^{138}$ extension
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
    have hxz := hInj x (.head _) z (.tail _ hzMem) hEq.symm
    exact hNotMem z hzMem hxz.symm

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

/-- **Irreducibility & Batch-Sacrifice Soundness of $\mathbb{F}_q[X]/(X^6 - 7)$ (`rss_mpc.rs:53-56, 1066-1206`)**:
    1. Serret–Kummer binomial irreducibility certificate for $X^6 - 7$ over $\mathbb{F}_{8380417}$:
       $6 \mid (q - 1)$, $7^{(q-1)/2} \equiv q - 1 \not\equiv 1 \pmod q$ ($7$ is a quadratic non-residue),
       $7^{(q-1)/3} \not\equiv 1 \pmod q$ ($7$ is a cubic non-residue), and $2^{138} < q^6$.
    2. Unique `Ext6Fq204` batch root: for any nonzero base-field gate error $\Delta \ne 0$ and arbitrary
       batch accumulator `rest`, `ext6Add rest (ext6Scale chi Δ) = ext6Zero` holds for **at most 1**
       challenge `chi : Ext6Fq204` (`(ext6BatchChallengeEquiv Δ hΔ rest).invFun ext6Zero`).
    3. Recursive polynomial folding bound (`rss_mpc.rs:1120-1171`, `FOLD = 8`): any degree-$\le D$
       ($D + 1 < q$) folding discrepancy polynomial with a nonzero coefficient has $\le D$ roots
       in any duplicate-free point set `S : List Fq204`. -/
theorem rss_ext6_irreducibility_and_batch_sacrifice_sound :
    ((mldsaQ - 1) % 6 = 0 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 2) = mldsaQ - 1 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 2) ≠ 1 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 3) ≠ 1 ∧
     2 ^ 138 < mldsaQ ^ 6) ∧
    (∀ (delta : Fq204) (hDelta : delta ≠ Fq204.zero) (rest chi₁ chi₂ : Ext6Fq204),
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
  | v :: vs => addVec4 v (rssSumVec4List vs)

private theorem matVecMul4_rssZeroVec4 (A : PolyMat4) :
    matVecMul4 A rssZeroVec4 = rssZeroVec4 := by
  funext i
  dsimp only [matVecMul4, rssZeroVec4]
  have hMul0 : ∀ p : Poly256, negacyclicMul p (PolyTree.zero 8) = PolyTree.zero 8 :=
    LawfulCommRing.mul_zero
  rw [hMul0, hMul0, hMul0, hMul0, polyTree_add_zero, polyTree_add_zero, polyTree_add_zero]

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
    ∀ (vs : List PolyVec4),
      matVecMul4 A (rssSumVec4List vs) = rssSumVec4List (vs.map (matVecMul4 A))
  | [] => matVecMul4_rssZeroVec4 A
  | v :: vs => by
    simp only [rssSumVec4List, List.map_cons, matVecMul4_add, matVecMul4_rssSumVec4List A vs]

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
    (∀ (t m : Nat) (subset corrupt : List (Fin m)),
      1 ≤ t → 2 * t - 1 ≤ m →
      subset.Nodup → subset.length = m - t + 1 → corrupt.length ≤ t - 1 →
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
  · intro t m subset corrupt ht hm hNd hSubLen hCorLen
    exact subset_honest_holder_exists t m ht hm subset corrupt hNd hSubLen hCorLen
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
      have hFrEq := cshake256FramedPreimage_frames_injective (by decide) (by decide) hAll1 hAll2 hPreEq
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

/-- Non-vacuity witness for `premature_z_release_leaks_s2_boundary` with nonzero `(A, s1, s2, y, c)`. -/
theorem premature_z_release_leaks_s2_boundary_inhabited :
    ∃ (A : PolyMat4) (_s1 s2 y : PolyVec4) (c : Poly256),
      c ≠ PolyTree.zero 8 ∧
      mldsa44Gamma2 - mldsa44Beta ≤ lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2)) := by
  let yHi : PolyVec4 := fun _ => polyTreeConstLeaf 8 ⟨95200, by decide⟩
  let z0 : PolyVec4 := fun _ => PolyTree.zero 8
  refine ⟨idMat4, z0, z0, yHi, PolyTree.constUnit 8, by decide, ?_⟩
  have hMv : matVecMul4 idMat4 yHi = yHi := matVecMul4_idMat4 yHi
  have hMul0 : mulPolyVec4 (PolyTree.constUnit 8) z0 = z0 := by
    funext i; exact negacyclicMul_one_left (z0 i)
  rw [hMv, hMul0]
  have hSub0 : subVec4 yHi z0 = yHi := by
    funext i; dsimp only [subVec4, z0]
    rw [polyTree_sub_eq_add_neg, ← polyTreeConstLeaf_zero_eq 8, polyTreeConstLeaf_neg]
    have hNeg0 : Fq204.neg Fq204.zero = Fq204.zero := by decide
    rw [hNeg0, polyTreeConstLeaf_zero_eq 8, polyTree_add_zero]
  rw [hSub0]
  unfold lowBitsNormVec4
  dsimp only [yHi]
  simp only [polyTreeConstLeaf_lowBitsNorm, Nat.max_self]
  decide

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

/-- **Standalone NIST FIPS 204 `ML-DSA-44` Verifier (`mldsaVerify`, `Algorithm 8`)**:
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
    key vectors `(s1Subsets, s2Subsets)` (never reconstructing `s1` or `s2` in the clear). -/
structure RssMlDsaSignerState where
  epoch : Nat
  nextAttempt : Nat
  A : PolyMat4
  s1Subsets : List PolyVec4
  s2Subsets : List PolyVec4

/-- Single RSS signing-attempt input (`threshold_mldsa.rs:795-975`):
    binds `(epoch, sessionId, attempt)`, message representative `mu`, RSS nonce shares `ySubsets`,
    fresh `< q` RSS masks `(maskW, maskZ, maskLow)`, and the `Ext6Fq204` multiplication-sacrifice bit. -/
structure RssMlDsaAttemptInput where
  epoch : Nat
  sessionId : List UInt8
  attempt : Nat
  mu : List UInt8
  ySubsets : List PolyVec4
  maskW : PolyVec4
  maskZ : PolyVec4
  maskLow : PolyVec4
  mpcSacrificeOk : Bool

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

/-- Triple `< q` RSS mask bijection over `(maskW, maskZ, maskLow)`. -/
def rssMaskTripleEquiv (w z u : PolyVec4) :
    SimpleEquiv (PolyVec4 × PolyVec4 × PolyVec4) (PolyVec4 × PolyVec4 × PolyVec4) :=
  SimpleEquiv.prod (rssMaskAddEquiv w) (SimpleEquiv.prod (rssMaskAddEquiv z) (rssMaskAddEquiv u))

/-- Explicit leakage-parameterized abort simulator (`threshold_mldsa.rs:940-1015`):
    given **only** the public ideal abort leakage `(leakedW1, rejectBit := true, usedAttempt)` and uniform
    simulator masks `simMasks` (zero secret shares `s1Subsets, s2Subsets, ySubsets`!), produces the exact
    `RssSignPublicAbortView` distribution of a rejected RSS signing attempt. -/
def rssAbortSimulator
    (leakedW1 : Fin 4 → NatTree 8) (usedAttempt : Nat)
    (simMasks : PolyVec4 × PolyVec4 × PolyVec4) : RssSignPublicAbortView :=
  { openedMaskedW := simMasks.1
    openedW1 := leakedW1
    openedMaskedZ := simMasks.2.1
    openedMaskedLow := simMasks.2.2
    rejectBit := true
    usedAttempt := usedAttempt }

/-- Per-attempt RSS transition of `threshold_sign_mldsa_party` (`threshold_mldsa.rs:795-1055`):
    - Enforces `(inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt)` and immediately burns
      `nextAttempt := st.nextAttempt + 1` BEFORE Phase 1;
    - Requires `inp.mpcSacrificeOk = true` (`Ext6Fq204` `verify_all_pending` + view-digest unanimity);
    - Evaluates `w1 = HighBits(w)`, `c = SampleInBall(H(μ, w1))`, and the RSS rejection predicate
      `accept`;
    - On rejection (`accept = false`), emits `(publicView, none)` (`rejectBit = true`, unmasked `z` NEVER opened!);
    - On acceptance (`accept = true`), emits `(publicView, some sig)` (`rejectBit = false`). -/
def rssThresholdSignStep
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    StepOutcome RssMlDsaSignerState
      (RssSignPublicAbortView × Option ThresholdSignSig)
      RssPreOpenAbortReason :=
  if inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt then
    let stBurned : RssMlDsaSignerState := { st with nextAttempt := st.nextAttempt + 1 }
    if inp.mpcSacrificeOk = true then
      let s1 := rssSumVec4List st.s1Subsets
      let s2 := rssSumVec4List st.s2Subsets
      let y := rssSumVec4List inp.ySubsets
      let t := addVec4 (matVecMul4 st.A s1) s2
      let t0 := power2RoundLowVec4 t
      let w := matVecMul4 st.A y
      let w1 := highBitsVec4 w
      let cTilde := chalHash inp.mu w1
      let c := sampleInBall cTilde
      let ct0 := mulPolyVec4 c t0
      let z := addVec4 y (mulPolyVec4 c s1)
      let u := subVec4 w (mulPolyVec4 c s2)
      let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
      let accept : Bool :=
        decide (infNormVec4 ct0 < mldsa44Gamma2) &&
        decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
        decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
        decide (hintWeightVec4 h ≤ mldsa44Omega)
      let publicView : RssSignPublicAbortView :=
        { openedMaskedW := addVec4 w inp.maskW
          openedW1 := w1
          openedMaskedZ := addVec4 z inp.maskZ
          openedMaskedLow := addVec4 u inp.maskLow
          rejectBit := !accept
          usedAttempt := inp.attempt }
      if accept = true then
        .ok stBurned (publicView, some { cTilde := cTilde, z := z, h := h, usedAttempt := inp.attempt })
      else
        .ok stBurned (publicView, none)
    else
      .err stBurned .mpcSacrificeFailed
  else
    .err st .attemptReplay

/-- Canonical `SimulationSpine.PartyMachine` instantiation of `rssThresholdSignStep`. -/
def rssThresholdSignMachine
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    PartyMachine RssMlDsaSignerState RssMlDsaAttemptInput
      (RssSignPublicAbortView × Option ThresholdSignSig) :=
  PartyMachine.ofOutcome (rssThresholdSignStep chalHash sampleInBall)

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
  unfold rssThresholdSignStep at hOk
  if hGate : inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt then
    rw [ite_true_of hGate] at hOk
    dsimp only at hOk
    if hSac : inp.mpcSacrificeOk = true then
      rw [ite_true_of hSac] at hOk
      let s1 := rssSumVec4List st.s1Subsets
      let s2 := rssSumVec4List st.s2Subsets
      let y := rssSumVec4List inp.ySubsets
      let t := addVec4 (matVecMul4 st.A s1) s2
      let t0 := power2RoundLowVec4 t
      let w := matVecMul4 st.A y
      let w1 := highBitsVec4 w
      let cTilde := chalHash inp.mu w1
      let c := sampleInBall cTilde
      let ct0 := mulPolyVec4 c t0
      let z := addVec4 y (mulPolyVec4 c s1)
      let u := subVec4 w (mulPolyVec4 c s2)
      let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
      let accept : Bool :=
        decide (infNormVec4 ct0 < mldsa44Gamma2) &&
        decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
        decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
        decide (hintWeightVec4 h ≤ mldsa44Omega)
      if hAcc : accept = true then
        rw [ite_true_of hAcc] at hOk
        injection hOk with hSt hOut
        injection hOut with hPub hSigOpt
        rw [← hSt, ← hPub]
        refine ⟨hGate.1, hGate.2, rfl, rfl, hGate.2, ?_⟩
        intro sig hSome
        rw [← hSigOpt] at hSome
        injection hSome with hSigEq
        rw [← hSigEq]
        dsimp only
        rw [hAcc]
        have hAccProps :
            ((infNormVec4 ct0 < mldsa44Gamma2 ∧ infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) ∧
             centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) ∧
            hintWeightVec4 h ≤ mldsa44Omega := by
          dsimp only [accept] at hAcc
          simpa only [Bool.and_eq_true, decide_eq_true_eq] using hAcc
        rcases hAccProps with ⟨⟨⟨hCt0Lt, hzLt⟩, hDiffLt⟩, hWeightLe⟩
        have hB : mldsa44Gamma2 - mldsa44Beta ≤ 95232 := by decide
        obtain ⟨hLowLt, hHighEq⟩ := (centeredDiffNormVec4_lt_iff u w hB).mp hDiffLt
        refine ⟨rfl, hGate.2, ?_⟩
        unfold mldsaVerify
        dsimp only
        have hUseHint := highBits_az_sub_ct_eq_w1 st.A s1 s2 y c mldsa44Beta hLowLt hCt0Lt
        dsimp only at hUseHint
        rw [hUseHint, hHighEq]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hzLt, hWeightLe⟩, rfl⟩
      else
        rw [ite_false_of hAcc] at hOk
        injection hOk with hSt hOut
        injection hOut with hPub hSigOpt
        rw [← hSt, ← hPub]
        refine ⟨hGate.1, hGate.2, rfl, rfl, hGate.2, ?_⟩
        intro sig hSome
        rw [← hSigOpt] at hSome
        cases hSome
    else
      rw [ite_false_of hSac] at hOk; cases hOk
  else
    rw [ite_false_of hGate] at hOk; cases hOk

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
    unfold rssThresholdSignStep at hOut
    if hGate : inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt then
      rw [ite_true_of hGate] at hOut
      dsimp only at hOut
      if hSac : inp.mpcSacrificeOk = true then
        rw [ite_true_of hSac] at hOut
        split at hOut <;> cases hOut
      else
        rw [ite_false_of hSac] at hOut
        injection hOut with hSt _
        rw [← hSt]; dsimp only; exact ⟨by omega, fun _ => rfl⟩
    else
      rw [ite_false_of hGate] at hOut
      injection hOut with hSt _
      rw [← hSt]
      exact ⟨Nat.le_refl _, fun hg => False.elim (hGate hg)⟩

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

/-- **Flagship §2.4 Theorem — `(t, m)` RSS Rejection-Sampling Leakage Simulator, Durable Nonce-Burn &
    Standalone FIPS 204 Completeness (`threshold_mldsa_rss_abort_leakage_and_completeness`, fixing `C0-1`)**:
    1. **Honest Abort Transcript & Unmasked-`z` Suppression (`rejectBit = true`)**: Whenever a valid
       attempt (`inp.epoch = st.epoch`, `inp.attempt = st.nextAttempt`, `inp.mpcSacrificeOk = true`)
       violates `‖z‖_∞ < γ₁ - β`, `‖LowBits(w - c*s2)‖_∞ < γ₂ - β`, or `HighBits(w - c*s2) = HighBits(w)`,
       `rssThresholdSignStep` emits `(pubView, none)` (`pubView.rejectBit = true`, `pubView.openedW1 = HighBits(w)`,
       unmasked `(z, h)` NEVER opened!) and burns `st'.nextAttempt = st.nextAttempt + 1`.
    2. **Explicit Leakage-Parameterized Abort Simulation (`rssAbortSimulator` + `rssMaskTripleEquiv`)**:
       Conditioned on the exact ideal abort leakage `(HighBits(w), rejectBit := true, inp.attempt)`,
       the `< q` RSS masks `(maskW, maskZ, maskLow)` map onto `(openedMaskedW, openedMaskedZ, openedMaskedLow)`
       via the constructive group bijection `rssMaskTripleEquiv w z u`, so `rssAbortSimulator` reproduces
       `pubView` identically with **zero** access to secret shares `(s1Subsets, s2Subsets, ySubsets)`!
    3. **Multi-Turn Attempt-Burn Uniqueness (`PartyMachine.ValidTrace`)**: Across ANY multi-turn trace of
       interleaved rejected and accepted attempts, `nextAttempt` is monotonically non-decreasing and every
       emitted transcript uses a strictly distinct `usedAttempt` index.
    4. **100% Standalone FIPS 204 `mldsaVerify` Completeness**: Every accepted signature `some sig` satisfies
       `pubView.rejectBit = false` and `mldsaVerify = true` under the RSS aggregate public key! -/
theorem threshold_mldsa_rss_abort_leakage_and_completeness
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    let M := rssThresholdSignMachine chalHash sampleInBall
    (∀ (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput),
      inp.epoch = st.epoch →
      inp.attempt = st.nextAttempt →
      inp.mpcSacrificeOk = true →
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
    unfold rssThresholdSignStep
    rw [ite_true_of ⟨hEp, hAtt⟩, ite_true_of hSac]
    dsimp only
    have hAccNeTrue : ¬ (decide (infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))) < mldsa44Gamma2) &&
         decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
         decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
         decide (hintWeightVec4 (makeHintVec4
           (negVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))))
           (addVec4 u (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))))) ≤ mldsa44Omega)) = true := by
      rw [hAccFalse]; decide
    rw [ite_false_of hAccNeTrue, hAccFalse]
    rfl
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
      pubRej.rejectBit = true := by
  let chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8 := fun mu _ => mu
  let sampleInBall : List UInt8 → Poly256 := fun _ => PolyTree.constUnit 8
  let p1 : Poly256 := polyTreeConstLeaf 8 Fq204.one
  let v1 : PolyVec4 := fun _ => p1
  let yBad : PolyVec4 := fun _ => polyTreeConstLeaf 8 ⟨131072, by decide⟩
  let st : RssMlDsaSignerState :=
    { epoch := 0, nextAttempt := 0, A := idMat4, s1Subsets := [v1], s2Subsets := [v1] }
  let inpAcc : RssMlDsaAttemptInput :=
    { epoch := 0, sessionId := [0x01], attempt := 0, mu := [0x42],
      ySubsets := [v1], maskW := rssZeroVec4, maskZ := rssZeroVec4, maskLow := rssZeroVec4,
      mpcSacrificeOk := true }
  let inpRej : RssMlDsaAttemptInput :=
    { epoch := 0, sessionId := [0x01], attempt := 0, mu := [0x42],
      ySubsets := [yBad], maskW := v1, maskZ := v1, maskLow := v1,
      mpcSacrificeOk := true }
  have hSum1 : rssSumVec4List [v1] = v1 := by
    dsimp only [rssSumVec4List]; exact addVec4_rssZero_right v1
  have hSumBad : rssSumVec4List [yBad] = yBad := by
    dsimp only [rssSumVec4List]; exact addVec4_rssZero_right yBad
  have hMv : matVecMul4 idMat4 v1 = v1 := matVecMul4_idMat4 v1
  have hMul1 : ∀ w : PolyVec4, mulPolyVec4 (PolyTree.constUnit 8) w = w := fun w => by
    funext i; exact negacyclicMul_one_left (w i)
  have hAddV1 : addVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 (Fq204.add Fq204.one Fq204.one)) := by
    funext i; exact polyTreeConstLeaf_add Fq204.one Fq204.one 8
  have hSubSelf : subVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 Fq204.zero) := by
    funext i; dsimp only [subVec4, v1]
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm, polyTree_add_left_neg, polyTreeConstLeaf_zero_eq]
  have hCt0 : infNormVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 idMat4 v1) v1))) <
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
  have hDiff : centeredDiffNormVec4 (subVec4 (matVecMul4 idMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
      (highBitsVec4 (matVecMul4 idMat4 v1)) < mldsa44Gamma2 - mldsa44Beta := by
    rw [hMv, hMul1, hSubSelf]
    unfold centeredDiffNormVec4 highBitsVec4
    dsimp only [v1, p1]
    simp only [polyTreeConstLeaf_centeredDiffNorm, Nat.max_self]
    decide
  have hW : hintWeightVec4 (makeHintVec4
      (negVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 idMat4 v1) v1))))
      (addVec4 (subVec4 (matVecMul4 idMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
               (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 idMat4 v1) v1))))) ≤
      mldsa44Omega := by
    rw [hMv, hMul1, hMul1, hSubSelf, hAddV1]
    unfold hintWeightVec4 makeHintVec4 negVec4 addVec4 power2RoundLowVec4
    dsimp only
    simp only [polyTreeConstLeaf_power2RoundLow, polyTreeConstLeaf_neg,
      polyTreeConstLeaf_add, polyTreeConstLeaf_hintWeight]
    decide
  have hAcc :
      (decide (infNormVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 idMat4 v1) v1))) < mldsa44Gamma2) &&
       decide (infNormVec4 (addVec4 v1 (mulPolyVec4 (PolyTree.constUnit 8) v1)) < mldsa44Gamma1 - mldsa44Beta) &&
       decide (centeredDiffNormVec4 (subVec4 (matVecMul4 idMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
         (highBitsVec4 (matVecMul4 idMat4 v1)) < mldsa44Gamma2 - mldsa44Beta) &&
       decide (hintWeightVec4 (makeHintVec4
         (negVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 idMat4 v1) v1))))
         (addVec4 (subVec4 (matVecMul4 idMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
                  (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 idMat4 v1) v1))))) ≤ mldsa44Omega)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hCt0, hZ⟩, hDiff⟩, hW⟩
  have hZBad : ¬ (infNormVec4 (addVec4 (rssSumVec4List inpRej.ySubsets)
      (mulPolyVec4 (sampleInBall (chalHash inpRej.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpRej.ySubsets)))))
        (rssSumVec4List st.s1Subsets))) < mldsa44Gamma1 - mldsa44Beta) := by
    dsimp only [st, inpRej, sampleInBall]
    rw [hSumBad, hSum1, hMul1]
    have hAddBad : addVec4 yBad v1 = (fun _ => polyTreeConstLeaf 8 (Fq204.add ⟨131072, by decide⟩ Fq204.one)) := by
      funext i; exact polyTreeConstLeaf_add ⟨131072, by decide⟩ Fq204.one 8
    rw [hAddBad]
    unfold infNormVec4
    dsimp only
    simp only [polyTreeConstLeaf_infNorm, Nat.max_self]
    decide
  obtain ⟨stRej, pubRej, hStepRej, _, hRejBit, _, _⟩ :=
    (threshold_mldsa_rss_abort_leakage_and_completeness chalHash sampleInBall).1 st inpRej rfl rfl rfl (Or.inl hZBad)
  cases hOutAcc : rssThresholdSignStep chalHash sampleInBall st inpAcc with
  | err _ _ =>
    exfalso
    unfold rssThresholdSignStep at hOutAcc
    dsimp only [st, inpAcc, sampleInBall] at hOutAcc
    rw [ite_true_of ⟨rfl, rfl⟩, ite_true_of rfl] at hOutAcc
    dsimp only at hOutAcc
    rw [hSum1, hSum1] at hOutAcc
    rw [ite_true_of hAcc] at hOutAcc
    cases hOutAcc
  | ok stAcc outPair =>
    rcases outPair with ⟨pubAcc, mSig⟩
    cases mSig with
    | none =>
      exfalso
      unfold rssThresholdSignStep at hOutAcc
      dsimp only [st, inpAcc, sampleInBall] at hOutAcc
      rw [ite_true_of ⟨rfl, rfl⟩, ite_true_of rfl] at hOutAcc
      dsimp only at hOutAcc
      rw [hSum1, hSum1, ite_true_of hAcc] at hOutAcc
      injection hOutAcc with _ hP
      injection hP with _ hNone
      cases hNone
    | some sig =>
      have hStepAcc : (rssThresholdSignMachine chalHash sampleInBall).step st inpAcc = some (stAcc, (pubAcc, some sig)) := by
        dsimp only [rssThresholdSignMachine, PartyMachine.ofOutcome]
        rw [hOutAcc]
      obtain ⟨hRejFalse, hVer⟩ :=
        (threshold_mldsa_rss_abort_leakage_and_completeness chalHash sampleInBall).2.2 _ _ _ _ _ hStepAcc
      exact ⟨chalHash, sampleInBall, st, stAcc, stRej, inpAcc, inpRej, pubAcc, pubRej, sig,
             hStepAcc, hRejFalse, hVer, hStepRej, hRejBit⟩

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

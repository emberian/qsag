module
public import Qsag.Tactic.Prelude
public import Qsag.Math.Algebra
public import Qsag.Math.Primality
public import Qsag.Math.CyclotomicRlwe

public section
namespace Qsag
set_option autoImplicit false
/-- NIST FIPS 204 prime modulus $q = 8380417 = 2^{23} - 2^{13} + 1 = 1023 \cdot 2^{13} + 1$. -/
abbrev mldsaQ : Nat := 8380417

/-- Cyclotomic ring degree $N = 256$. -/
abbrev mldsaN : Nat := 256

/-- Dropped public-key low-order bit width $d = 13$ ($2^{13} = 8192$). -/
abbrev mldsaD : Nat := 13

/-- Primitive 512-th root of unity $\zeta = 1753 \in \mathbb{Z}_q$ ($\zeta^{256} \equiv -1 \pmod q$). -/
abbrev mldsaZetaNat : Nat := 1753

/-- `ML-DSA-44` (`FIPS 204` Category 2) parameter constants. -/
abbrev mldsa44Gamma2 : Nat := 95232        -- (q - 1) / 88
abbrev mldsa44Alpha : Nat := 190464        -- 2 * gamma2 = (q - 1) / 44
abbrev mldsa44HighMod : Nat := 44          -- (q - 1) / alpha
abbrev mldsa44Tau : Nat := 39
abbrev mldsa44Eta : Nat := 2
abbrev mldsa44Omega : Nat := 80
abbrev mldsa44K : Nat := 4
abbrev mldsa44L : Nat := 4

/-! ### §1.1 Constructive Primality Certificate for `mldsaQ = 8380417` -/

/-- Exported primality witness structure on `Nat` (`0` `@[expose]` overhead). -/
abbrev IsPrime204 := IsPrimeNat
namespace IsPrime204
theorem ge_two {p : Nat} (h : IsPrime204 p) : 2 ≤ p := h.1
theorem dvd_cases {p : Nat} (h : IsPrime204 p) (d : Nat) (hd : d ∣ p) : d = 1 ∨ d = p := h.2 d hd
end IsPrime204

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
    (hdvd : p ∣ a * b) (hna : ¬ (p ∣ a)) : p ∣ b := IsPrimeNat.dvd_mul hp hdvd hna

/-! ### §1.2 Canonical Field `Fq204`, Barrett Multiplication & Constructive Bézout Inversion -/

/-- Canonical element of $\mathbb{Z}_q$ ($q = 8380417$). -/
abbrev Fq204 := ModZq mldsaQ

namespace Fq204
abbrev mk (v : Nat) (h : v < mldsaQ) : Fq204 := ModZq.mk v h

theorem ext {a b : Fq204} (h : a.val = b.val) : a = b := by
  exact ModZq.ext h

@[expose] def ofNat (n : Nat) : Fq204 :=
  ⟨n % mldsaQ, Nat.mod_lt n (by decide)⟩

@[expose] def zero : Fq204 := ⟨0, by decide⟩
@[expose] def one : Fq204 := ⟨1, by decide⟩

instance : Inhabited Fq204 := ⟨zero⟩

@[simp] theorem zero_val : zero.val = 0 := by rfl
@[simp] theorem one_val : one.val = 1 := by rfl
@[simp] theorem ofNat_val (n : Nat) : (ofNat n).val = n % mldsaQ := by rfl

@[expose] def add (a b : Fq204) : Fq204 :=
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

@[expose] def neg (a : Fq204) : Fq204 :=
  if h : a.val = 0 then ⟨0, by decide⟩ else ⟨mldsaQ - a.val, by have := a.isLt; omega⟩

theorem neg_val (a : Fq204) : (neg a).val = (mldsaQ - a.val) % mldsaQ := by
  unfold neg
  have ha := a.isLt
  if h0 : a.val = 0 then
    simp [h0]
  else
    simp only [h0, ↓reduceDIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

@[expose] def sub (a b : Fq204) : Fq204 :=
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

@[expose] def mul (a b : Fq204) : Fq204 :=
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

@[expose] def ofInt (z : Int) : Fq204 :=
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
@[expose] def toCenteredInt (a : Fq204) : Int :=
  if a.val ≤ mldsaQ / 2 then (a.val : Int) else (a.val : Int) - (mldsaQ : Int)

/-- Infinity-norm magnitude $|a \bmod^\pm q| \in [0, 4190208]$. -/
@[expose] def centeredAbs (a : Fq204) : Nat :=
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
    have hval : (a.val * b.val) % mldsaQ = 0 := congrArg ModZq.val h
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
@[expose] def pow (a : Fq204) : Nat → Fq204
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
@[expose] def inv (a : Fq204) : Fq204 :=
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
  inv_zero := by decide
  mul_inv_cancel := Fq204.mul_inv_cancel

/-! ### §1.3 256-Point Negacyclic Ring $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$ & 8-Stage NTT Isomorphism -/

/-- Primitive 512-th root $\zeta = 1753 \in \mathbb{Z}_{8380417}$. -/
abbrev mldsaZeta : Fq204 := ⟨1753, by decide⟩

/-- Multiplicative inverse $2^{-1} \equiv 4190209 \pmod{8380417}$. -/
abbrev mldsaInv2 : Fq204 := ⟨4190209, by decide⟩

/-- Multiplicative inverse $256^{-1} \equiv 8347681 \pmod{8380417}$. -/
abbrev mldsaInv256 : Fq204 := ⟨8347681, by decide⟩

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


end Qsag

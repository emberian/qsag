module
/-
# Qsag.PallasAndBlsMigration — Zcash Orchard (`Pallas` / `RedPallas`) & Ethereum Beacon (`BLS12-381`) PQ Ownership Migration

Constructive (`0 Classical.choice`, `0 native_decide`, `0 sorry`) formalization of:
1. Exact curve and field parameters for Zcash Orchard `Pallas` (`y^2 = x^3 + 5` over `p_pallas`,
   scalar field `q_pallas`, `orchardSpendAuthG`) and Ethereum Beacon `BLS12-381` (`y^2 = x^3 + 4`
   over `381`-bit `p_bls381`, prime subgroup order `r_bls381`, IETF generator `bls381G1`),
   matching the little-endian limb tables in `pallas.rs` and `bls12_381.rs`.
2. General constructive Lucas–Pratt primality verifier (`checkPrattStep_sound`,
   `checkPrattDAG_sound`) via eager binary modular exponentiation (`powModFuel`), certifying
   primality of `p_pallas`, `q_pallas`, `r_bls381`, and `p_bls381` in the Lean kernel, paired
   with a Carmichael `561` mutation witness (`tooth_carmichael_561_passes_fermat_but_fails_pratt`).
3. Curve membership and prime subgroup annihilation (`[q_pallas] SpendAuthG = O`,
   `[r_bls381] G_1 = O`) via complete projective Renes–Costello–Batina addition (`rcbAdd`),
   paired with the `BLS12-381` 3-torsion subgroup counterexample `(0, 2)`
   (`tooth_bls381_torsion3_onCurve_but_off_subgroup`).
4. 3-party ZKBoo 2-of-3 special-soundness discrete-log extraction (`zkboo_two_challenge_extraction_sound`),
   Zcash Orchard RedPallas rerandomized `rk = [ask + alpha] SpendAuthG` homomorphic binding
   extraction (`orchard_redpallas_rerandomized_extraction_sound`), and fiber-bijection
   unlinkability (`orchard_redpallas_rk_perfect_unlinkability`) paired with `#tooth` witnesses.
-/

public import Qsag.Goldilocks
public import Qsag.ActiveMigrationZeroTest
public import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

set_option autoImplicit false

/-! ## 1. Exact `Pallas` (`Orchard`) & `BLS12-381` (`Beacon`) Parameters and Limb Equivalence -/

/-- Zcash Pasta `Pallas` base field modulus `p = 2^254 + 0x224698fc094cf91b992d30ed00000001`. -/
@[expose] def p_pallas : Nat :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

/-- Zcash Pasta `Pallas` scalar field modulus `q = 2^254 + 0x224698fc0994a8dd8c46eb2100000001`. -/
@[expose] def q_pallas : Nat :=
  0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

/-- Ethereum Beacon `BLS12-381` base field modulus `p` (`381` bits). -/
@[expose] def p_bls381 : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- Ethereum Beacon `BLS12-381` prime subgroup order `r` (`255` bits). -/
@[expose] def r_bls381 : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- Reconstruct a 384-bit integer from 6 little-endian `UInt64` limbs (`BLS_P`, `BLS_G1_GX`, `BLS_G1_GY`). -/
def limbs6LeToNat (limbs : Fin 6 → UInt64) : Nat :=
  (limbs ⟨0, by decide⟩).toNat +
  (limbs ⟨1, by decide⟩).toNat * (2 ^ 64) +
  (limbs ⟨2, by decide⟩).toNat * (2 ^ 128) +
  (limbs ⟨3, by decide⟩).toNat * (2 ^ 192) +
  (limbs ⟨4, by decide⟩).toNat * (2 ^ 256) +
  (limbs ⟨5, by decide⟩).toNat * (2 ^ 320)

def pallasPLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0x992d30ed00000001
  | ⟨1, _⟩ => 0x224698fc094cf91b
  | ⟨2, _⟩ => 0x0000000000000000
  | ⟨3, _⟩ => 0x4000000000000000

def pallasQLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0x8c46eb2100000001
  | ⟨1, _⟩ => 0x224698fc0994a8dd
  | ⟨2, _⟩ => 0x0000000000000000
  | ⟨3, _⟩ => 0x4000000000000000

def bls381PLimbsLe : Fin 6 → UInt64
  | ⟨0, _⟩ => 0xb9feffffffffaaab
  | ⟨1, _⟩ => 0x1eabfffeb153ffff
  | ⟨2, _⟩ => 0x6730d2a0f6b0f624
  | ⟨3, _⟩ => 0x64774b84f38512bf
  | ⟨4, _⟩ => 0x4b1ba7b6434bacd7
  | ⟨5, _⟩ => 0x1a0111ea397fe69a

def bls381RLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0xffffffff00000001
  | ⟨1, _⟩ => 0x53bda402fffe5bfe
  | ⟨2, _⟩ => 0x3339d80809a1d805
  | ⟨3, _⟩ => 0x73eda753299d7d48

/-- Zcash `Pallas` short-Weierstrass curve `y^2 = x^3 + 5` over `ℤ / p_pallas ℤ`. -/
@[expose] def pallasCurve : Weierstrass.Curve :=
  { p := p_pallas, a := 0, b := 5 }

/-- Official Zcash Orchard `SpendAuthG` affine point (`ORCHARD_SPEND_AUTH_GX`, `ORCHARD_SPEND_AUTH_GY`). -/
def orchardSpendAuthG : Weierstrass.Point :=
  some (0x375523b328f1d6063b8d187c3e5f445f0c7f0ce37b70a10c8d1a7284b875c963,
        0x1ad0357fdf1a66db7b10bcfcfed624fbdfc914fec005bdd84ce33e817b0c3bc9)

/-- Pasta cycle standard `Pallas` generator `(-1, 2)`. -/
def pastaPallasG : Weierstrass.Point :=
  some (p_pallas - 1, 2)

/-- Ethereum Beacon `BLS12-381` short-Weierstrass curve `y^2 = x^3 + 4` over `ℤ / p_bls381 ℤ`. -/
@[expose] def bls381Curve : Weierstrass.Curve :=
  { p := p_bls381, a := 0, b := 4 }

/-- Official IETF / Ethereum Beacon `BLS12-381` `G_1` affine generator (`BLS_G1_GX`, `BLS_G1_GY`). -/
def bls381G1 : Weierstrass.Point :=
  some (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
        0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)

theorem pallas_and_bls381_limbs_and_bit_bounds :
    limbs4LeToNat pallasPLimbsLe = p_pallas ∧
    limbs4LeToNat pallasQLimbsLe = q_pallas ∧
    limbs6LeToNat bls381PLimbsLe = p_bls381 ∧
    limbs4LeToNat bls381RLimbsLe = r_bls381 ∧
    2 ^ 254 < p_pallas ∧ p_pallas < 2 ^ 255 ∧ p_pallas % 2 = 1 ∧
    2 ^ 254 < q_pallas ∧ q_pallas < 2 ^ 255 ∧ q_pallas % 2 = 1 ∧
    2 ^ 380 < p_bls381 ∧ p_bls381 < 2 ^ 381 ∧ p_bls381 % 4 = 3 ∧
    2 ^ 254 < r_bls381 ∧ r_bls381 < 2 ^ 255 ∧ r_bls381 % 2 = 1 := by
  unfold limbs4LeToNat limbs6LeToNat pallasPLimbsLe pallasQLimbsLe bls381PLimbsLe bls381RLimbsLe
    p_pallas q_pallas p_bls381 r_bls381
  decide

/-! ## 2. Constructive Lucas–Pratt Primality Certificates (`0 native_decide`, `0 Classical.choice`) -/

private def strictNat (n : Nat) (k : Nat → Nat) : Nat :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

private theorem strictNat_eq (n : Nat) (k : Nat → Nat) : strictNat n k = k n := by
  cases n <;> rfl

/-- Eager binary modular exponentiation `base ^ exp % m` in `fuel` squaring steps. -/
def powModFuel : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | fuel + 1, base, exp, m =>
    if exp = 0 then 1 % m
    else
      strictNat (powModFuel fuel base (exp / 2) m) fun half =>
        strictNat ((half * half) % m) fun sq =>
          if exp % 2 = 1 then (sq * (base % m)) % m else sq

private theorem pow_two_mul_local (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem powModFuel_eq_pow_mod :
    ∀ (fuel base exp m : Nat), exp < 2 ^ fuel → powModFuel fuel base exp m = (base ^ exp) % m
  | 0, _, exp, m, hlt => by
    have he0 : exp = 0 := by simp at hlt; omega
    subst he0; simp [powModFuel]
  | fuel + 1, base, exp, m, hlt => by
    simp only [powModFuel]
    if h0 : exp = 0 then
      subst h0; simp
    else
      simp only [h0, ↓reduceIte, strictNat_eq]
      have hexpHalf : exp / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hlt; omega
      have ih := powModFuel_eq_pow_mod fuel base (exp / 2) m hexpHalf
      have hsq : ((powModFuel fuel base (exp / 2) m) * (powModFuel fuel base (exp / 2) m)) % m =
          (base ^ (2 * (exp / 2))) % m := by
        rw [ih, ← Nat.mul_mod, ← pow_two_mul_local]
      rcases (by omega : exp % 2 = 0 ∨ exp % 2 = 1) with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide, ↓reduceIte]
        have hexp : 2 * (exp / 2) = exp := by omega
        rw [hsq, hexp]
      · simp only [hr1, ↓reduceIte]
        have hexp : exp = 2 * (exp / 2) + 1 := by omega
        conv => rhs; rw [hexp, Nat.pow_add, Nat.pow_one, Nat.mul_mod]
        rw [hsq]

def powNatStrict (b : Nat) : Nat → Nat
  | 0 => 1
  | e + 1 => strictNat (powNatStrict b e) fun p => b * p

private theorem powNatStrict_eq (b : Nat) : ∀ e : Nat, powNatStrict b e = b ^ e
  | 0 => rfl
  | e + 1 => by
    simp only [powNatStrict, strictNat_eq, powNatStrict_eq b e, Nat.pow_succ, Nat.mul_comm]

/-- Eagerly evaluated prime-power factorization product $\prod_{(q, e)} q^e$. -/
def facProd : List (Nat × Nat) → Nat
  | [] => 1
  | (q, e) :: rest =>
    strictNat (powNatStrict q e) fun qe =>
      strictNat (facProd rest) fun tail =>
        qe * tail

/-- A Lucas–Pratt primality certificate node `(n, g, facs)` for `n - 1 = facProd facs`. -/
structure PrattCert where
  n : Nat
  g : Nat
  facs : List (Nat × Nat)

/-- Executable Boolean verifier for one Lucas–Pratt certificate step. -/
def checkPrattStep (knownPrimes : List Nat) (c : PrattCert) : Bool :=
  decide (3 ≤ c.n) &&
  decide (c.n < 2 ^ 384) &&
  (facProd c.facs == c.n - 1) &&
  c.facs.all (fun qe => decide (1 ≤ qe.2) && knownPrimes.any (fun p => p == qe.1)) &&
  (powModFuel 384 c.g (c.n - 1) c.n == 1) &&
  c.facs.all (fun qe => powModFuel 384 c.g ((c.n - 1) / qe.1) c.n != 1)

/-- Executable Boolean verifier for a topologically ordered Lucas–Pratt certificate DAG. -/
def checkPrattDAG : List Nat → List PrattCert → Bool
  | _, [] => true
  | known, c :: rest =>
    checkPrattStep known c && checkPrattDAG (c.n :: known) rest

private def minPrimeDivAux (n d : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n % d = 0 then d else minPrimeDivAux n (d + 1) fuel

private def minPrimeDiv (n : Nat) : Nat :=
  if n < 2 then n else minPrimeDivAux n 2 n

private theorem minPrimeDivAux_spec :
    ∀ (fuel n d : Nat),
      2 ≤ n → 2 ≤ d → n ≤ d + fuel →
      (∀ k : Nat, 2 ≤ k → k < d → ¬ (k ∣ n)) →
      let q := minPrimeDivAux n d fuel
      2 ≤ q ∧ q ∣ n ∧ (∀ k : Nat, 2 ≤ k → k < q → ¬ (k ∣ n))
  | 0, n, d, hn2, _, _, hno => by
    dsimp only [minPrimeDivAux]
    exact ⟨hn2, Nat.dvd_refl n, fun k hk2 hklt => hno k hk2 (by omega)⟩
  | fuel + 1, n, d, hn2, hd, hle, hno => by
    dsimp only [minPrimeDivAux]
    if hmod : n % d = 0 then
      simp only [hmod, ↓reduceIte]
      exact ⟨hd, Nat.dvd_of_mod_eq_zero hmod, hno⟩
    else
      simp only [hmod, ↓reduceIte]
      apply minPrimeDivAux_spec fuel n (d + 1) hn2 (by omega) (by omega)
      intro k hk2 hklt
      if hkd : k = d then
        subst hkd; exact fun hdvd => hmod (Nat.mod_eq_zero_of_dvd hdvd)
      else exact hno k hk2 (by omega)

private theorem minPrimeDiv_isPrime {n : Nat} (hn : 2 ≤ n) :
    IsPrimeNat (minPrimeDiv n) ∧ minPrimeDiv n ∣ n := by
  unfold minPrimeDiv
  have hnot : ¬ n < 2 := by omega
  simp only [hnot, ↓reduceIte]
  obtain ⟨hq2, hqdvd, hqmin⟩ := minPrimeDivAux_spec n n 2 hn (by decide) (by omega) (by intros; omega)
  refine ⟨⟨hq2, ?_⟩, hqdvd⟩
  intro d hd
  if hd1 : d = 1 then exact .inl hd1
  else if hdq : d = minPrimeDivAux n 2 n then exact .inr hdq
  else
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    have hdle : d ≤ minPrimeDivAux n 2 n := Nat.le_of_dvd (by omega) hd
    exact False.elim (hqmin d (by omega) (by omega) (Nat.dvd_trans hd hqdvd))

private theorem prime_dvd_pow {p q : Nat} (hp : IsPrimeNat p) :
    ∀ e : Nat, p ∣ q ^ e → p ∣ q
  | 0, hd => by
    have hle := Nat.le_of_dvd (by decide) hd
    have hp2 := hp.1
    omega
  | e + 1, hd => by
    rw [Nat.pow_succ] at hd
    if hpq : p ∣ q then exact hpq
    else exact prime_dvd_pow hp e (hp.dvd_mul (Nat.mul_comm (q ^ e) q ▸ hd) hpq)

private theorem prime_mem_of_dvd_facProd {p : Nat} (hp : IsPrimeNat p) :
    ∀ {facs : List (Nat × Nat)},
      (∀ qe ∈ facs, IsPrimeNat qe.1) →
      p ∣ facProd facs →
      ∃ qe ∈ facs, qe.1 = p
  | [], _, hd => by
    dsimp only [facProd] at hd
    have hle := Nat.le_of_dvd (by decide) hd
    have hp2 := hp.1
    omega
  | (q, e) :: rest, hPrimes, hd => by
    simp only [facProd, strictNat_eq, powNatStrict_eq] at hd
    if hdq : p ∣ q ^ e then
      have hpq : p ∣ q := prime_dvd_pow hp e hdq
      have hqPrime : IsPrimeNat q := hPrimes (q, e) (.head _)
      rcases hqPrime.2 p hpq with hp1 | hpEq
      · have hp2 := hp.1; omega
      · exact ⟨(q, e), .head _, hpEq.symm⟩
    else
      obtain ⟨qe, hMem, hEq⟩ := prime_mem_of_dvd_facProd hp
        (fun x hx => hPrimes x (.tail _ hx)) (hp.dvd_mul hd hdq)
      exact ⟨qe, .tail _ hMem, hEq⟩

private def minOrderAux (g N cur : Nat) : Nat → Nat
  | 0 => cur
  | fuel + 1 => if (g ^ cur) % N = 1 then cur else minOrderAux g N (cur + 1) fuel

private theorem minOrderAux_spec (g N : Nat) :
    ∀ (fuel cur : Nat),
      1 ≤ cur →
      (g ^ (cur + fuel)) % N = 1 →
      (∀ k : Nat, 1 ≤ k → k < cur → (g ^ k) % N ≠ 1) →
      let d := minOrderAux g N cur fuel
      1 ≤ d ∧ d ≤ cur + fuel ∧ (g ^ d) % N = 1 ∧ (∀ k : Nat, 1 ≤ k → k < d → (g ^ k) % N ≠ 1)
  | 0, cur, hcur, hEnd, hMin => by
    dsimp only [minOrderAux]
    rw [Nat.add_zero] at hEnd
    exact ⟨hcur, Nat.le_refl cur, hEnd, hMin⟩
  | fuel + 1, cur, hcur, hEnd, hMin => by
    dsimp only [minOrderAux]
    if h1 : (g ^ cur) % N = 1 then
      simp only [h1, ↓reduceIte]
      exact ⟨hcur, by omega, h1, hMin⟩
    else
      simp only [h1, ↓reduceIte]
      have hEnd' : (g ^ ((cur + 1) + fuel)) % N = 1 := by
        have heq : (cur + 1) + fuel = cur + (fuel + 1) := by omega
        rwa [heq]
      have res := minOrderAux_spec g N fuel (cur + 1) (by omega) hEnd' (fun k hk1 hklt => by
        if hkc : k = cur then subst hkc; exact h1
        else exact hMin k hk1 (by omega))
      exact ⟨res.1, by omega, res.2.2.1, res.2.2.2⟩

private theorem pow_mod_eq_one_rep {a N : Nat} (hN : 2 ≤ N) (ha : a % N = 1) :
    ∀ q : Nat, (a ^ q) % N = 1
  | 0 => Nat.mod_eq_of_lt hN
  | q + 1 => by
    rw [Nat.pow_succ, Nat.mul_mod, pow_mod_eq_one_rep hN ha q, ha]
    exact Nat.mod_eq_of_lt hN

private theorem order_dvd_of_pow_eq_one {g N d0 m : Nat}
    (hN : 2 ≤ N) (hd0 : 1 ≤ d0) (hPow0 : (g ^ d0) % N = 1)
    (hMin : ∀ k : Nat, 1 ≤ k → k < d0 → (g ^ k) % N ≠ 1)
    (hPowM : (g ^ m) % N = 1) : d0 ∣ m := by
  have hDiv : d0 * (m / d0) + m % d0 = m := Nat.div_add_mod m d0
  have hRemPow : (g ^ (m % d0)) % N = 1 := by
    have hm' : (g ^ (d0 * (m / d0) + m % d0)) % N = 1 := hDiv.symm ▸ hPowM
    rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod,
        pow_mod_eq_one_rep hN hPow0 (m / d0), Nat.one_mul, Nat.mod_mod] at hm'
    exact hm'
  if hRem0 : m % d0 = 0 then
    exact Nat.dvd_of_mod_eq_zero hRem0
  else
    exact False.elim (hMin (m % d0) (by omega) (Nat.mod_lt m (by omega)) hRemPow)

private def posRangeP : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: posRangeP n

private theorem mem_posRangeP_iff {x : Nat} : ∀ {n : Nat}, x ∈ posRangeP n ↔ 1 ≤ x ∧ x ≤ n
  | 0 => ⟨fun h => nomatch h, fun ⟨h1, h2⟩ => by omega⟩
  | n + 1 => by
    simp only [posRangeP, List.mem_cons, mem_posRangeP_iff]
    constructor
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Nat.succ_pos n, Nat.le_refl _⟩
      · exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      if heq : x = n + 1 then exact .inl heq else exact .inr ⟨h1, by omega⟩

private theorem posRangeP_length : ∀ n : Nat, (posRangeP n).length = n
  | 0 => rfl
  | n + 1 => by simp [posRangeP, posRangeP_length n]

private theorem posRangeP_nodup : ∀ n : Nat, (posRangeP n).Nodup
  | 0 => .nil
  | n + 1 => .cons (fun b hb heq => by have := (mem_posRangeP_iff.1 hb).2; omega) (posRangeP_nodup n)

private def eraseOne (v : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if y = v then ys else y :: eraseOne v ys

private theorem mem_of_mem_eraseOne {v z : Nat} : ∀ {ys : List Nat}, z ∈ eraseOne v ys → z ∈ ys
  | [], h => nomatch h
  | y :: ys, h => by
    dsimp only [eraseOne] at h
    split at h
    · exact .tail _ h
    · cases h with
      | head => exact .head _
      | tail _ ht => exact .tail _ (mem_of_mem_eraseOne ht)

private theorem eraseOne_spec {v : Nat} :
    ∀ {ys : List Nat}, ys.Nodup → v ∈ ys →
      (eraseOne v ys).length + 1 = ys.length ∧
      (eraseOne v ys).Nodup ∧
      (∀ z : Nat, z ≠ v → z ∈ ys → z ∈ eraseOne v ys)
  | [], _, hmem => nomatch hmem
  | y :: ys, .cons hrel hnd, hmem => by
    dsimp only [eraseOne]
    if hy : y = v then
      subst hy
      simp only [↓reduceIte, List.length_cons]
      refine ⟨rfl, hnd, fun z hzne hz => ?_⟩
      cases hz with
      | head => exact False.elim (hzne rfl)
      | tail _ ht => exact ht
    else
      simp only [hy, ↓reduceIte, List.length_cons]
      have hvTail : v ∈ ys := by
        cases hmem with
        | head => exact False.elim (hy rfl)
        | tail _ ht => exact ht
      obtain ⟨hlen, hnd', hsub⟩ := eraseOne_spec hnd hvTail
      refine ⟨by omega, .cons (fun b hb heq => hrel b (mem_of_mem_eraseOne hb) heq) hnd', ?_⟩
      intro z hzne hz
      cases hz with
      | head => exact .head _
      | tail _ ht => exact .tail _ (hsub z hzne ht)

private theorem mem_of_nodup_subset_eq_length :
    ∀ {xs ys : List Nat},
      xs.Nodup → ys.Nodup → xs.length = ys.length →
      (∀ x ∈ xs, x ∈ ys) → ∀ y ∈ ys, y ∈ xs
  | [], [], _, _, _, _, _, hy => nomatch hy
  | [], _ :: _, _, _, hlen, _, _, _ => nomatch hlen
  | x :: xs, ys, .cons hrel hndX, hndY, hlen, hsub, y, hy => by
    if hyx : y = x then
      subst hyx; exact .head _
    else
      obtain ⟨hlenE, hndE, hmemE⟩ := eraseOne_spec hndY (hsub x (.head _))
      simp only [List.length_cons] at hlen
      have hSub' : ∀ z ∈ xs, z ∈ eraseOne x ys := fun z hz =>
        hmemE z (fun heq => hrel z hz heq.symm) (hsub z (.tail _ hz))
      exact .tail _ (mem_of_nodup_subset_eq_length hndX hndE (by omega) hSub' y (hmemE y hyx hy))

/-- **Lucas–Pratt Theorem (`isPrime_of_lucas_pratt`)**: if `g^(N-1) ≡ 1 (mod N)` and
    `g^((N-1)/q) ≢ 1 (mod N)` for every prime factor `q` of `N - 1`, then `N` is prime. -/
theorem isPrime_of_lucas_pratt {N g : Nat} {facs : List (Nat × Nat)}
    (hN3 : 3 ≤ N)
    (hProd : facProd facs = N - 1)
    (hPrimes : ∀ qe ∈ facs, IsPrimeNat qe.1)
    (hFermat : (g ^ (N - 1)) % N = 1)
    (hOrder : ∀ qe ∈ facs, (g ^ ((N - 1) / qe.1)) % N ≠ 1) :
    IsPrimeNat N := by
  have hN2 : 2 ≤ N := by omega
  have hEnd : (g ^ (1 + (N - 2))) % N = 1 := by
    have heq : 1 + (N - 2) = N - 1 := by omega
    rwa [heq]
  obtain ⟨hd1, hdLe, hdPow, hdMin⟩ :=
    minOrderAux_spec g N (N - 2) 1 (by decide) hEnd (by intros; omega)
  set d0 := minOrderAux g N 1 (N - 2)
  have hdLeNm1 : d0 ≤ N - 1 := by omega
  have hdDvdNm1 : d0 ∣ (N - 1) := order_dvd_of_pow_eq_one hN2 hd1 hdPow hdMin hFermat
  have hdEqNm1 : d0 = N - 1 := by
    if hEq : d0 = N - 1 then exact hEq
    else
      exfalso
      obtain ⟨c, hc⟩ := hdDvdNm1
      have hc2 : 2 ≤ c := by
        if hc0 : c = 0 then rw [hc0, Nat.mul_zero] at hc; omega
        else if hc1 : c = 1 then rw [hc1, Nat.mul_one] at hc; exact hEq hc.symm
        else omega
      obtain ⟨hpPrime, hpDvdC⟩ := minPrimeDiv_isPrime hc2
      set p := minPrimeDiv c
      obtain ⟨c', hc'⟩ := hpDvdC
      have hNm1Eq : N - 1 = p * (d0 * c') := by
        rw [hc, hc', ← Nat.mul_assoc d0 p c', Nat.mul_comm d0 p, Nat.mul_assoc]
      have hpDvdFac : p ∣ facProd facs := by rw [hProd, hNm1Eq]; exact Nat.dvd_mul_right p _
      obtain ⟨qe, hqeMem, hqeEq⟩ := prime_mem_of_dvd_facProd hpPrime hPrimes hpDvdFac
      have hDivEq : (N - 1) / p = d0 * c' := by
        rw [hNm1Eq, Nat.mul_comm p (d0 * c')]
        exact Nat.mul_div_left (d0 * c') (by have := hpPrime.1; omega)
      have hPow1 : (g ^ ((N - 1) / qe.1)) % N = 1 := by
        rw [hqeEq, hDivEq, Nat.pow_mul]
        exact pow_mod_eq_one_rep hN2 hdPow c'
      exact hOrder qe hqeMem hPow1
  rw [hdEqNm1] at hdMin
  let L := posRangeP (N - 1)
  let f := fun k : Nat => (g ^ k) % N
  have hMapMem : ∀ x ∈ L.map f, x ∈ L := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hk1, hkHi⟩ := mem_posRangeP_iff.1 hk
    have hfkLt : (g ^ k) % N < N := Nat.mod_lt _ (by omega)
    have hfkPos : 1 ≤ (g ^ k) % N := by
      if hz : (g ^ k) % N = 0 then
        have hdvdK : N ∣ g ^ k := Nat.dvd_of_mod_eq_zero hz
        have hSum : k + (N - 1 - k) = N - 1 := by omega
        have hdvdNm1 : N ∣ g ^ (N - 1) := by
          rw [← hSum, Nat.pow_add]
          exact Nat.dvd_mul_right_of_dvd hdvdK _
        have h0 : (g ^ (N - 1)) % N = 0 := Nat.mod_eq_zero_of_dvd hdvdNm1
        omega
      else omega
    exact mem_posRangeP_iff.2 ⟨hfkPos, by omega⟩
  have hInjStep : ∀ i j : Nat, 1 ≤ i → i < j → j ≤ N - 1 → f i = f j → False := by
    intro i j hi1 hij hjHi hEqF
    have hMulEq : ((g ^ j % N) * (g ^ (N - 1 - i) % N)) % N =
        ((g ^ i % N) * (g ^ (N - 1 - i) % N)) % N := by
      dsimp only [f] at hEqF; rw [hEqF]
    rw [← Nat.mul_mod, ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_add] at hMulEq
    have hRhs : i + (N - 1 - i) = N - 1 := by omega
    have hLhs : j + (N - 1 - i) = (N - 1) + (j - i) := by omega
    rw [hRhs, hLhs, Nat.pow_add, Nat.mul_mod, hFermat, Nat.one_mul, Nat.mod_mod, hFermat] at hMulEq
    exact hdMin (j - i) (by omega) (by omega) hMulEq
  have hInj : ∀ i j : Nat, i ∈ L → j ∈ L → f i = f j → i = j := by
    intro i j hi hj hij
    obtain ⟨hi1, hiHi⟩ := mem_posRangeP_iff.1 hi
    obtain ⟨hj1, hjHi⟩ := mem_posRangeP_iff.1 hj
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · exact False.elim (hInjStep i j hi1 hlt hjHi hij)
    · exact heq
    · exact False.elim (hInjStep j i hj1 hgt hiHi hij.symm)
  have hMapNodup : (L.map f).Nodup := by
    have aux : ∀ {xs : List Nat}, xs.Nodup → (∀ z ∈ xs, z ∈ L) → (xs.map f).Nodup := by
      intro xs hnd hxs
      induction hnd with
      | nil => exact .nil
      | @cons a rest hrel hndR ih =>
        refine .cons (fun b hb heq => ?_) (ih (fun z hz => hxs z (.tail _ hz)))
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
        exact hrel y hy (hInj a y (hxs a (.head _)) (hxs y (.tail _ hy)) heq)
    exact aux (posRangeP_nodup (N - 1)) (fun z hz => hz)
  have hSurj : ∀ y ∈ L, y ∈ L.map f :=
    mem_of_nodup_subset_eq_length hMapNodup (posRangeP_nodup (N - 1)) (List.length_map f) hMapMem
  refine ⟨hN2, fun d hd => ?_⟩
  if hd1' : d = 1 then exact .inl hd1'
  else if hdN : d = N then exact .inr hdN
  else
    exfalso
    have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    have hdLeN : d ≤ N := Nat.le_of_dvd (by omega) hd
    have hdMemL : d ∈ L := mem_posRangeP_iff.2 ⟨by omega, by omega⟩
    obtain ⟨k, hkMem, hfkEq⟩ := List.mem_map.1 (hSurj d hdMemL)
    obtain ⟨hk1, hkHi⟩ := mem_posRangeP_iff.1 hkMem
    dsimp only [f] at hfkEq
    have hDivK : N * (g ^ k / N) + (g ^ k) % N = g ^ k := Nat.div_add_mod (g ^ k) N
    rw [hfkEq] at hDivK
    have hdGk : d ∣ g ^ k := by
      rw [← hDivK]
      exact Nat.dvd_add (Nat.dvd_trans hd (Nat.dvd_mul_right N _)) (Nat.dvd_refl d)
    have hSumK : k + (N - 1 - k) = N - 1 := by omega
    have hdGNm1 : d ∣ g ^ (N - 1) := by
      rw [← hSumK, Nat.pow_add]
      exact Nat.dvd_mul_right_of_dvd hdGk _
    have hDivNm1 : N * (g ^ (N - 1) / N) + (g ^ (N - 1)) % N = g ^ (N - 1) :=
      Nat.div_add_mod (g ^ (N - 1)) N
    rw [hFermat] at hDivNm1
    obtain ⟨u, hu⟩ := hd
    obtain ⟨v, hv⟩ := hdGNm1
    have hd1Dvd : d ∣ 1 := by
      refine ⟨v - u * (g ^ (N - 1) / N), ?_⟩
      rw [Nat.mul_sub, ← hv, ← Nat.mul_assoc d u _, ← hu]
      omega
    have := Nat.le_of_dvd (by decide) hd1Dvd
    omega

/-- Soundness of the executable `checkPrattStep` verifier (`0 Classical.choice`). -/
theorem checkPrattStep_sound {known : List Nat} {c : PrattCert}
    (hKnown : ∀ p ∈ known, IsPrimeNat p)
    (hCheck : checkPrattStep known c = true) :
    IsPrimeNat c.n := by
  unfold checkPrattStep at hCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
    List.all_eq_true, List.any_eq_true] at hCheck
  rcases hCheck with ⟨⟨⟨⟨⟨h3, hLt⟩, hProd⟩, hFacs⟩, hFerm⟩, hOrd⟩
  have hExpNm1 : c.n - 1 < 2 ^ 384 := by omega
  rw [powModFuel_eq_pow_mod 384 c.g (c.n - 1) c.n hExpNm1] at hFerm
  apply isPrime_of_lucas_pratt h3 hProd
  · intro qe hMem
    obtain ⟨_, p, hpMem, hpEq⟩ := hFacs qe hMem
    exact hpEq ▸ hKnown p hpMem
  · exact hFerm
  · intro qe hMem
    have hDivLt : (c.n - 1) / qe.1 < 2 ^ 384 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hExpNm1
    have hNe := hOrd qe hMem
    rwa [powModFuel_eq_pow_mod 384 c.g ((c.n - 1) / qe.1) c.n hDivLt] at hNe

/-- Soundness of the executable `checkPrattDAG` verifier across any certificate chain. -/

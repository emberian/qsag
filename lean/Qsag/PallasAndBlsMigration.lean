module
/-
# Qsag.PallasAndBlsMigration — Zcash Orchard (`Pallas` / `RedPallas`) & Ethereum Beacon (`BLS12-381`) PQ Ownership Migration

Constructive (`0 Classical.choice`, `0 native_decide`, `0 sorry`) formalization of:
1. Exact `Pallas` (`y^2 = x^3 + 5`, `p_pallas`, `q_pallas`, `orchardSpendAuthG`) and `BLS12-381` (`y^2 = x^3 + 4`, `p_bls381`, `r_bls381`, `bls381G1`) parameters matching `pallas.rs` and `bls12_381.rs`.
2. Constructive Lucas–Pratt primality verifier (`checkPrattStep_sound`, `checkPrattDAG_sound`) via binary `lucasPowMod`, certifying `p_pallas`, `q_pallas`, `r_bls381`, `p_bls381`, paired with Carmichael `561` (`#tooth`).
3. Complete projective RCB addition (`rcbAdd`), curve membership, and prime subgroup annihilation (`[q_pallas] SpendAuthG = O`, `[r_bls381] G_1 = O`), paired with the `BLS12-381` 3-torsion point `(0, 2)` (`#tooth`).
4. 3-party ZKBoo 2-of-3 discrete-log extraction (`zkboo_two_challenge_extraction_sound`) and Zcash Orchard RedPallas rerandomized `rk = [ask + alpha] SpendAuthG` binding extraction & unlinkability (`#tooth`).
-/

public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
set_option autoImplicit false

/-! ## 1. Exact `Pallas` (`Orchard`) & `BLS12-381` (`Beacon`) Parameters and Limb Equivalence -/

@[expose] def p_pallas : Nat := 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
@[expose] def q_pallas : Nat := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001
@[expose] def p_bls381 : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
@[expose] def r_bls381 : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

def limbs4LeNat (limbs : Fin 4 → UInt64) : Nat :=
  (limbs ⟨0, by decide⟩).toNat + (limbs ⟨1, by decide⟩).toNat * (2 ^ 64) +
  (limbs ⟨2, by decide⟩).toNat * (2 ^ 128) + (limbs ⟨3, by decide⟩).toNat * (2 ^ 192)

def limbs6LeToNat (limbs : Fin 6 → UInt64) : Nat :=
  (limbs ⟨0, by decide⟩).toNat + (limbs ⟨1, by decide⟩).toNat * (2 ^ 64) +
  (limbs ⟨2, by decide⟩).toNat * (2 ^ 128) + (limbs ⟨3, by decide⟩).toNat * (2 ^ 192) +
  (limbs ⟨4, by decide⟩).toNat * (2 ^ 256) + (limbs ⟨5, by decide⟩).toNat * (2 ^ 320)

def pallasPLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0x992d30ed00000001 | ⟨1, _⟩ => 0x224698fc094cf91b | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 0x4000000000000000
def pallasQLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0x8c46eb2100000001 | ⟨1, _⟩ => 0x224698fc0994a8dd | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 0x4000000000000000
def bls381PLimbsLe : Fin 6 → UInt64
  | ⟨0, _⟩ => 0xb9feffffffffaaab | ⟨1, _⟩ => 0x1eabfffeb153ffff | ⟨2, _⟩ => 0x6730d2a0f6b0f624
  | ⟨3, _⟩ => 0x64774b84f38512bf | ⟨4, _⟩ => 0x4b1ba7b6434bacd7 | ⟨5, _⟩ => 0x1a0111ea397fe69a
def bls381RLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0xffffffff00000001 | ⟨1, _⟩ => 0x53bda402fffe5bfe
  | ⟨2, _⟩ => 0x3339d80809a1d805 | ⟨3, _⟩ => 0x73eda753299d7d48

structure SwCurve where
  p : Nat
  a : Nat
  b : Nat

abbrev SwPoint := Option (Nat × Nat)

@[expose] def SwCurve.onCurve (C : SwCurve) : SwPoint → Bool
  | none => true
  | some (x, y) => decide (x < C.p) && decide (y < C.p) && (((y * y) % C.p) == ((x * x * x + C.a * x + C.b) % C.p))

@[expose] def SwCurve.neg (C : SwCurve) : SwPoint → SwPoint
  | none => none | some (x, y) => some (x, (C.p - y) % C.p)

def pallasCurve : SwCurve := { p := p_pallas, a := 0, b := 5 }
def orchardSpendAuthG : SwPoint :=
  some (0x375523b328f1d6063b8d187c3e5f445f0c7f0ce37b70a10c8d1a7284b875c963,
        0x1ad0357fdf1a66db7b10bcfcfed624fbdfc914fec005bdd84ce33e817b0c3bc9)
def pastaPallasG : SwPoint := some (p_pallas - 1, 2)
def bls381Curve : SwCurve := { p := p_bls381, a := 0, b := 4 }
def bls381G1 : SwPoint :=
  some (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
        0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)

private def pow2_380 : Nat := (2 ^ 190) * (2 ^ 190)
private def pow2_381 : Nat := (2 ^ 190) * (2 ^ 191)
private def pow2_384 : Nat := (2 ^ 192) * (2 ^ 192)
private theorem pow2_384_eq : pow2_384 = 2 ^ 384 := by rw [pow2_384, ← Nat.pow_add]

theorem pallas_and_bls381_limbs_and_bit_bounds :
    limbs4LeNat pallasPLimbsLe = p_pallas ∧ limbs4LeNat pallasQLimbsLe = q_pallas ∧
    limbs6LeToNat bls381PLimbsLe = p_bls381 ∧ limbs4LeNat bls381RLimbsLe = r_bls381 ∧
    2 ^ 254 < p_pallas ∧ p_pallas < 2 ^ 255 ∧ p_pallas % 2 = 1 ∧
    2 ^ 254 < q_pallas ∧ q_pallas < 2 ^ 255 ∧ q_pallas % 2 = 1 ∧
    pow2_380 < p_bls381 ∧ p_bls381 < pow2_381 ∧ p_bls381 % 4 = 3 ∧
    2 ^ 254 < r_bls381 ∧ r_bls381 < 2 ^ 255 ∧ r_bls381 % 2 = 1 := by
  unfold limbs4LeNat limbs6LeToNat pallasPLimbsLe pallasQLimbsLe bls381PLimbsLe bls381RLimbsLe
    p_pallas q_pallas p_bls381 r_bls381 pow2_380 pow2_381
  decide

/-! ## 2. Constructive Lucas–Pratt Primality Certificates (`0 native_decide`, `0 Classical.choice`) -/

@[expose] def IsPrimeMod (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem IsPrimeMod.dvd_mul {p a b : Nat} (hp : IsPrimeMod p) (h : p ∣ a * b) (hna : ¬ (p ∣ a)) : p ∣ b := by
  rcases hp.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with h1 | hpg
  · exact Nat.Coprime.dvd_of_dvd_mul_left h1 h
  · exact False.elim (hna (hpg ▸ Nat.gcd_dvd_right p a))

private def strictNat (n : Nat) (k : Nat → Nat) : Nat := match n with | 0 => k 0 | m + 1 => k (m + 1)
private theorem strictNat_eq (n : Nat) (k : Nat → Nat) : strictNat n k = k n := by cases n <;> rfl

/-- Eager binary modular exponentiation `base ^ exp % m` in `fuel` squaring steps. -/
def lucasPowMod : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | fuel + 1, base, exp, m =>
    if exp = 0 then 1 % m
    else strictNat (lucasPowMod fuel base (exp / 2) m) fun half =>
      strictNat ((half * half) % m) fun sq => if exp % 2 = 1 then (sq * (base % m)) % m else sq

private theorem pow_two_mul_local (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem lucasPowMod_eq_pow_mod :
    ∀ (fuel base exp m : Nat), exp < 2 ^ fuel → lucasPowMod fuel base exp m = (base ^ exp) % m
  | 0, _, exp, m, hlt => by have he0 : exp = 0 := by simp at hlt; omega
                            subst he0; simp [lucasPowMod]
  | fuel + 1, base, exp, m, hlt => by
    simp only [lucasPowMod]
    if h0 : exp = 0 then subst h0; simp
    else
      simp only [h0, ↓reduceIte, strictNat_eq]
      have hexpHalf : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hlt; omega
      have ih := lucasPowMod_eq_pow_mod fuel base (exp / 2) m hexpHalf
      have hsq : ((lucasPowMod fuel base (exp / 2) m) * (lucasPowMod fuel base (exp / 2) m)) % m =
          (base ^ (2 * (exp / 2))) % m := by rw [ih, ← Nat.mul_mod, ← pow_two_mul_local]
      rcases (by omega : exp % 2 = 0 ∨ exp % 2 = 1) with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide, ↓reduceIte]; rw [hsq, show 2 * (exp / 2) = exp by omega]
      · simp only [hr1, ↓reduceIte]
        conv => rhs; rw [show exp = 2 * (exp / 2) + 1 by omega, Nat.pow_add, Nat.pow_one, Nat.mul_mod]
        rw [hsq]

private def powNatStrict (b : Nat) : Nat → Nat
  | 0 => 1 | e + 1 => strictNat (powNatStrict b e) fun p => b * p
private theorem powNatStrict_eq (b : Nat) : ∀ e : Nat, powNatStrict b e = b ^ e
  | 0 => rfl | e + 1 => by simp only [powNatStrict, strictNat_eq, powNatStrict_eq b e, Nat.pow_succ, Nat.mul_comm]

def lucasFacProd : List (Nat × Nat) → Nat
  | [] => 1
  | (q, e) :: rest => strictNat (powNatStrict q e) fun qe => strictNat (lucasFacProd rest) fun tail => qe * tail

structure PrattCert where
  n : Nat
  g : Nat
  facs : List (Nat × Nat)

def checkPrattStep (knownPrimes : List Nat) (c : PrattCert) : Bool :=
  decide (3 ≤ c.n) && decide (c.n < pow2_384) && (lucasFacProd c.facs == c.n - 1) &&
  c.facs.all (fun qe => decide (1 ≤ qe.2) && knownPrimes.any (fun p => p == qe.1)) &&
  (lucasPowMod 384 c.g (c.n - 1) c.n == 1) &&
  c.facs.all (fun qe => lucasPowMod 384 c.g ((c.n - 1) / qe.1) c.n != 1)

def checkPrattDAG : List Nat → List PrattCert → Bool
  | _, [] => true | known, c :: rest => checkPrattStep known c && checkPrattDAG (c.n :: known) rest

private def minPrimeDivAux (n d : Nat) : Nat → Nat
  | 0 => n | fuel + 1 => if n % d = 0 then d else minPrimeDivAux n (d + 1) fuel
private def minPrimeDiv (n : Nat) : Nat := if n < 2 then n else minPrimeDivAux n 2 n

private theorem minPrimeDivAux_spec :
    ∀ (fuel n d : Nat), 2 ≤ n → 2 ≤ d → n ≤ d + fuel → (∀ k : Nat, 2 ≤ k → k < d → ¬ (k ∣ n)) →
      let q := minPrimeDivAux n d fuel
      2 ≤ q ∧ q ∣ n ∧ (∀ k : Nat, 2 ≤ k → k < q → ¬ (k ∣ n))
  | 0, n, d, hn2, _, hle, hno => by
    dsimp only [minPrimeDivAux]; exact ⟨hn2, Nat.dvd_refl n, fun k hk2 hklt => hno k hk2 (by omega)⟩
  | fuel + 1, n, d, hn2, hd, hle, hno => by
    dsimp only [minPrimeDivAux]
    if hmod : n % d = 0 then rw [if_pos hmod]; exact ⟨hd, Nat.dvd_of_mod_eq_zero hmod, hno⟩
    else
      rw [if_neg hmod]
      refine minPrimeDivAux_spec fuel n (d + 1) hn2 (by omega) (by omega) (fun k hk2 hklt => ?_)
      exact if hkd : k = d then fun hdvd => hmod (Nat.mod_eq_zero_of_dvd (hkd ▸ hdvd)) else hno k hk2 (by omega)

private theorem minPrimeDiv_isPrime {n : Nat} (hn : 2 ≤ n) : IsPrimeMod (minPrimeDiv n) ∧ minPrimeDiv n ∣ n := by
  unfold minPrimeDiv; rw [if_neg (by omega : ¬ n < 2)]
  obtain ⟨hq2, hqdvd, hqmin⟩ := minPrimeDivAux_spec n n 2 hn (by decide) (by omega) (by intros; omega)
  refine ⟨⟨hq2, fun d hd => ?_⟩, hqdvd⟩
  if hd1 : d = 1 then exact .inl hd1
  else if hdq : d = minPrimeDivAux n 2 n then exact .inr hdq
  else
    have := Nat.pos_of_dvd_of_pos hd (by omega); have := Nat.le_of_dvd (by omega) hd
    exact False.elim (hqmin d (by omega) (by omega) (Nat.dvd_trans hd hqdvd))

private theorem prime_dvd_pow {p q : Nat} (hp : IsPrimeMod p) : ∀ e : Nat, p ∣ q ^ e → p ∣ q
  | 0, hd => by rw [Nat.pow_zero] at hd; have := Nat.le_of_dvd (by decide) hd; have := hp.1; omega
  | e + 1, hd => by
    rw [Nat.pow_succ] at hd
    exact if hpq : p ∣ q then hpq else prime_dvd_pow hp e (hp.dvd_mul (Nat.mul_comm _ _ ▸ hd) hpq)

private theorem prime_mem_of_dvd_facProd {p : Nat} (hp : IsPrimeMod p) :
    ∀ {facs : List (Nat × Nat)}, (∀ qe ∈ facs, IsPrimeMod qe.1) → p ∣ lucasFacProd facs → ∃ qe ∈ facs, qe.1 = p
  | [], _, hd => by dsimp only [lucasFacProd] at hd; have := Nat.le_of_dvd (by decide) hd; have := hp.1; omega
  | (q, e) :: rest, hPrimes, hd => by
    simp only [lucasFacProd, strictNat_eq, powNatStrict_eq] at hd
    if hdq : p ∣ q ^ e then
      rcases (hPrimes (q, e) (.head _)).2 p (prime_dvd_pow hp e hdq) with hp1 | hpEq
      · have := hp.1; omega
      · exact ⟨(q, e), .head _, hpEq.symm⟩
    else
      obtain ⟨qe, hMem, hEq⟩ := prime_mem_of_dvd_facProd hp (fun x hx => hPrimes x (.tail _ hx)) (hp.dvd_mul hd hdq)
      exact ⟨qe, .tail _ hMem, hEq⟩

private def minOrderAux (g N cur : Nat) : Nat → Nat
  | 0 => cur | fuel + 1 => if (g ^ cur) % N = 1 then cur else minOrderAux g N (cur + 1) fuel

private theorem minOrderAux_spec (g N : Nat) :
    ∀ (fuel cur : Nat), 1 ≤ cur → (g ^ (cur + fuel)) % N = 1 → (∀ k : Nat, 1 ≤ k → k < cur → (g ^ k) % N ≠ 1) →
      let d := minOrderAux g N cur fuel
      1 ≤ d ∧ d ≤ cur + fuel ∧ (g ^ d) % N = 1 ∧ (∀ k : Nat, 1 ≤ k → k < d → (g ^ k) % N ≠ 1)
  | 0, cur, hcur, hEnd, hMin => by dsimp only [minOrderAux]; exact ⟨hcur, Nat.le_refl cur, Nat.add_zero cur ▸ hEnd, hMin⟩
  | fuel + 1, cur, hcur, hEnd, hMin => by
    dsimp only [minOrderAux]
    if h1 : (g ^ cur) % N = 1 then rw [if_pos h1]; exact ⟨hcur, by omega, h1, hMin⟩
    else
      rw [if_neg h1]
      have res := minOrderAux_spec g N fuel (cur + 1) (by omega)
        (by rwa [show (cur + 1) + fuel = cur + (fuel + 1) by omega])
        (fun k hk1 hklt => if hkc : k = cur then hkc ▸ h1 else hMin k hk1 (by omega))
      exact ⟨res.1, by omega, res.2.2.1, res.2.2.2⟩

private theorem pow_mod_eq_one_rep {a N : Nat} (hN : 2 ≤ N) (ha : a % N = 1) : ∀ q : Nat, (a ^ q) % N = 1
  | 0 => Nat.mod_eq_of_lt hN
  | q + 1 => by rw [Nat.pow_succ, Nat.mul_mod, pow_mod_eq_one_rep hN ha q, ha]; exact Nat.mod_eq_of_lt hN

private theorem order_dvd_of_pow_eq_one {g N d0 m : Nat} (hN : 2 ≤ N) (hd0 : 1 ≤ d0) (hPow0 : (g ^ d0) % N = 1)
    (hMin : ∀ k : Nat, 1 ≤ k → k < d0 → (g ^ k) % N ≠ 1) (hPowM : (g ^ m) % N = 1) : d0 ∣ m := by
  have hm' : (g ^ (d0 * (m / d0) + m % d0)) % N = 1 := (Nat.div_add_mod m d0).symm ▸ hPowM
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, pow_mod_eq_one_rep hN hPow0 (m / d0), Nat.one_mul, Nat.mod_mod] at hm'
  exact if hRem0 : m % d0 = 0 then Nat.dvd_of_mod_eq_zero hRem0
        else False.elim (hMin (m % d0) (by omega) (Nat.mod_lt m (by omega)) hm')

private def posRangeP : Nat → List Nat | 0 => [] | n + 1 => (n + 1) :: posRangeP n

private theorem mem_posRangeP_iff {x : Nat} : ∀ {n : Nat}, x ∈ posRangeP n ↔ 1 ≤ x ∧ x ≤ n
  | 0 => ⟨fun h => nomatch h, fun ⟨_, _⟩ => by omega⟩
  | n + 1 => by
    simp only [posRangeP, List.mem_cons, mem_posRangeP_iff]
    refine ⟨?_, fun ⟨h1, h2⟩ => if heq : x = n + 1 then .inl heq else .inr ⟨h1, by omega⟩⟩
    rintro (rfl | ⟨h1, h2⟩); exact ⟨Nat.succ_pos n, Nat.le_refl _⟩; exact ⟨h1, by omega⟩

private theorem posRangeP_nodup : ∀ n : Nat, (posRangeP n).Nodup
  | 0 => .nil
  | n + 1 => .cons (fun _ hb heq => by have := (mem_posRangeP_iff.1 hb).2; omega) (posRangeP_nodup n)

private def eraseOne (v : Nat) : List Nat → List Nat
  | [] => [] | y :: ys => if y = v then ys else y :: eraseOne v ys

private theorem mem_of_mem_eraseOne {v z : Nat} : ∀ {ys : List Nat}, z ∈ eraseOne v ys → z ∈ ys
  | [], h => nomatch h
  | y :: ys, h => by
    dsimp only [eraseOne] at h; split at h
    · exact .tail _ h
    · cases h with | head => exact .head _ | tail _ ht => exact .tail _ (mem_of_mem_eraseOne ht)

private theorem eraseOne_spec {v : Nat} : ∀ {ys : List Nat}, ys.Nodup → v ∈ ys →
    (eraseOne v ys).length + 1 = ys.length ∧ (eraseOne v ys).Nodup ∧ (∀ z : Nat, z ≠ v → z ∈ ys → z ∈ eraseOne v ys)
  | [], _, hmem => nomatch hmem
  | y :: ys, .cons hrel hnd, hmem => by
    dsimp only [eraseOne]
    if hy : y = v then
      subst hy; rw [if_pos rfl]; refine ⟨rfl, hnd, fun z hzne hz => ?_⟩
      cases hz with | head => exact False.elim (hzne rfl) | tail _ ht => exact ht
    else
      rw [if_neg hy]
      have hvTail : v ∈ ys := by cases hmem with | head => exact False.elim (hy rfl) | tail _ ht => exact ht
      obtain ⟨hlen, hnd', hsub⟩ := eraseOne_spec hnd hvTail
      refine ⟨by simp only [List.length_cons]; omega,
        .cons (fun b hb heq => hrel b (mem_of_mem_eraseOne hb) heq) hnd', fun z hzne hz => ?_⟩
      cases hz with | head => exact .head _ | tail _ ht => exact .tail _ (hsub z hzne ht)

private theorem mem_of_nodup_subset_eq_length : ∀ {xs ys : List Nat}, xs.Nodup → ys.Nodup →
    xs.length = ys.length → (∀ x ∈ xs, x ∈ ys) → ∀ y ∈ ys, y ∈ xs
  | [], [], _, _, _, _, _, hy => nomatch hy
  | [], _ :: _, _, _, hlen, _, _, _ => nomatch hlen
  | x :: xs, ys, .cons hrel hndX, hndY, hlen, hsub, y, hy => by
    if hyx : y = x then subst hyx; exact .head _
    else
      obtain ⟨hlenE, hndE, hmemE⟩ := eraseOne_spec hndY (hsub x (.head _))
      simp only [List.length_cons] at hlen
      exact .tail _ (mem_of_nodup_subset_eq_length hndX hndE (by omega)
        (fun z hz => hmemE z (fun heq => hrel z hz heq.symm) (hsub z (.tail _ hz))) y (hmemE y hyx hy))

/-- **Lucas–Pratt Theorem (`isPrime_of_lucas_pratt`)**: exact prime-factor order witnesses imply `IsPrimeMod N`. -/
theorem isPrime_of_lucas_pratt {N g : Nat} {facs : List (Nat × Nat)}
    (hN3 : 3 ≤ N) (hProd : lucasFacProd facs = N - 1) (hPrimes : ∀ qe ∈ facs, IsPrimeMod qe.1)
    (hFermat : (g ^ (N - 1)) % N = 1) (hOrder : ∀ qe ∈ facs, (g ^ ((N - 1) / qe.1)) % N ≠ 1) : IsPrimeMod N := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hd1, hdLe, hdPow, hdMin⟩ := minOrderAux_spec g N (N - 2) 1 (by decide)
    (by rwa [show 1 + (N - 2) = N - 1 by omega]) (by intros; omega)
  set d0 := minOrderAux g N 1 (N - 2)
  have hdDvdNm1 : d0 ∣ (N - 1) := order_dvd_of_pow_eq_one hN2 hd1 hdPow hdMin hFermat
  have hdEqNm1 : d0 = N - 1 := by
    if hEq : d0 = N - 1 then exact hEq
    else
      exfalso; obtain ⟨c, hc⟩ := hdDvdNm1
      have hc2 : 2 ≤ c := by
        if hc0 : c = 0 then rw [hc0, Nat.mul_zero] at hc; omega
        else if hc1 : c = 1 then rw [hc1, Nat.mul_one] at hc; exact hEq hc.symm
        else omega
      obtain ⟨hpPrime, c', hc'⟩ := minPrimeDiv_isPrime hc2
      set p := minPrimeDiv c
      have hNm1Eq : N - 1 = p * (d0 * c') := by rw [hc, hc', ← Nat.mul_assoc d0 p c', Nat.mul_comm d0 p, Nat.mul_assoc]
      obtain ⟨qe, hqeMem, hqeEq⟩ := prime_mem_of_dvd_facProd hpPrime hPrimes (by rw [hProd, hNm1Eq]; exact Nat.dvd_mul_right p _)
      refine hOrder qe hqeMem ?_
      rw [hqeEq, hNm1Eq, Nat.mul_comm p (d0 * c'), Nat.mul_div_left (d0 * c') (by have := hpPrime.1; omega), Nat.pow_mul]
      exact pow_mod_eq_one_rep hN2 hdPow c'
  rw [hdEqNm1] at hdMin
  let L := posRangeP (N - 1); let f := fun k : Nat => (g ^ k) % N
  have hMapMem : ∀ x ∈ L.map f, x ∈ L := by
    intro x hx; obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx; obtain ⟨hk1, hkHi⟩ := mem_posRangeP_iff.1 hk
    have hfkLt : (g ^ k) % N < N := Nat.mod_lt _ (by omega)
    have hfkPos : 1 ≤ (g ^ k) % N := by
      if hz : (g ^ k) % N = 0 then
        have hdvdNm1 : N ∣ g ^ (N - 1) := by
          rw [show N - 1 = k + (N - 1 - k) by omega, Nat.pow_add]
          exact Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero hz) _
        have := Nat.mod_eq_zero_of_dvd hdvdNm1; omega
      else omega
    exact mem_posRangeP_iff.2 ⟨hfkPos, by omega⟩
  have hInjStep : ∀ i j : Nat, 1 ≤ i → i < j → j ≤ N - 1 → f i = f j → False := by
    intro i j hi1 hij hjHi hEqF
    have hMulEq : ((g ^ j % N) * (g ^ (N - 1 - i) % N)) % N = ((g ^ i % N) * (g ^ (N - 1 - i) % N)) % N := by
      dsimp only [f] at hEqF; rw [hEqF]
    rw [← Nat.mul_mod, ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_add,
        show i + (N - 1 - i) = N - 1 by omega, show j + (N - 1 - i) = (N - 1) + (j - i) by omega,
        Nat.pow_add, Nat.mul_mod, hFermat, Nat.one_mul, Nat.mod_mod, hFermat] at hMulEq
    exact hdMin (j - i) (by omega) (by omega) hMulEq
  have hMapNodup : (L.map f).Nodup := by
    have aux : ∀ {xs : List Nat}, xs.Nodup → (∀ z ∈ xs, z ∈ L) → (xs.map f).Nodup := by
      intro xs hnd hxs; induction hnd with
      | nil => exact .nil
      | @cons a rest hrel _ ih =>
        refine .cons (fun b hb heq => ?_) (ih (fun z hz => hxs z (.tail _ hz)))
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
        obtain ⟨ha1, haHi⟩ := mem_posRangeP_iff.1 (hxs a (.head _))
        obtain ⟨hy1, hyHi⟩ := mem_posRangeP_iff.1 (hxs y (.tail _ hy))
        rcases Nat.lt_trichotomy a y with hlt | hEq | hgt
        · exact hInjStep a y ha1 hlt hyHi heq
        · exact hrel y hy hEq
        · exact hInjStep y a hy1 hgt haHi heq.symm
    exact aux (posRangeP_nodup (N - 1)) (fun z hz => hz)
  have hSurj := mem_of_nodup_subset_eq_length hMapNodup (posRangeP_nodup (N - 1)) (List.length_map f) hMapMem
  refine ⟨hN2, fun d hd => ?_⟩
  if hd1' : d = 1 then exact .inl hd1'
  else if hdN : d = N then exact .inr hdN
  else
    exfalso
    have hdPos := Nat.pos_of_dvd_of_pos hd (by omega); have hdLeN := Nat.le_of_dvd (by omega) hd
    obtain ⟨k, hkMem, hfkEq⟩ := List.mem_map.1 (hSurj d (mem_posRangeP_iff.2 ⟨by omega, by omega⟩))
    obtain ⟨hk1, hkHi⟩ := mem_posRangeP_iff.1 hkMem; dsimp only [f] at hfkEq
    have hDivK := Nat.div_add_mod (g ^ k) N; rw [hfkEq] at hDivK
    have hdGk : d ∣ g ^ k := by rw [← hDivK]; exact Nat.dvd_add (Nat.dvd_trans hd (Nat.dvd_mul_right N _)) (Nat.dvd_refl d)
    have hdGNm1 : d ∣ g ^ (N - 1) := by
      rw [show N - 1 = k + (N - 1 - k) by omega, Nat.pow_add]; exact Nat.dvd_mul_right_of_dvd hdGk _
    have hDivNm1 := Nat.div_add_mod (g ^ (N - 1)) N; rw [hFermat] at hDivNm1
    obtain ⟨u, hu⟩ := hd; obtain ⟨v, hv⟩ := hdGNm1
    have hd1Dvd : d ∣ 1 := ⟨v - u * (g ^ (N - 1) / N), by rw [Nat.mul_sub, ← hv, ← Nat.mul_assoc d u _, ← hu]; omega⟩
    have := Nat.le_of_dvd (by decide) hd1Dvd; omega

theorem checkPrattStep_sound {known : List Nat} {c : PrattCert}
    (hKnown : ∀ p ∈ known, IsPrimeMod p) (hCheck : checkPrattStep known c = true) : IsPrimeMod c.n := by
  unfold checkPrattStep at hCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, List.all_eq_true, List.any_eq_true] at hCheck
  rcases hCheck with ⟨⟨⟨⟨⟨h3, hLt⟩, hProd⟩, hFacs⟩, hFerm⟩, hOrd⟩
  rw [pow2_384_eq] at hLt; have hExpNm1 : c.n - 1 < 2 ^ 384 := by omega
  rw [lucasPowMod_eq_pow_mod 384 c.g (c.n - 1) c.n hExpNm1] at hFerm
  refine isPrime_of_lucas_pratt h3 hProd (fun qe hMem => ?_) hFerm (fun qe hMem => ?_)
  · obtain ⟨_, p, hpMem, hpEq⟩ := hFacs qe hMem; exact hpEq ▸ hKnown p hpMem
  · have hDivLt : (c.n - 1) / qe.1 < 2 ^ 384 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hExpNm1
    have hNe := hOrd qe hMem; rwa [lucasPowMod_eq_pow_mod 384 c.g ((c.n - 1) / qe.1) c.n hDivLt] at hNe

theorem checkPrattDAG_sound : ∀ (certs : List PrattCert) (known : List Nat),
    (∀ p ∈ known, IsPrimeMod p) → checkPrattDAG known certs = true → ∀ c ∈ certs, IsPrimeMod c.n
  | [], _, _, _, _, hc => nomatch hc
  | c :: rest, known, hKnown, hOk, target, hMem => by
    unfold checkPrattDAG at hOk; rw [Bool.and_eq_true] at hOk
    have hcPrime : IsPrimeMod c.n := checkPrattStep_sound hKnown hOk.1
    cases hMem with
    | head => exact hcPrime
    | tail _ hTail =>
      refine checkPrattDAG_sound rest (c.n :: known) (fun p hp => ?_) hOk.2 target hTail
      cases hp with | head => exact hcPrime | tail _ hIn => exact hKnown p hIn

/-- `#tooth` Carmichael `561` passes `2^560 ≡ 1 (mod 561)` yet `checkPrattStep` deterministically rejects it. -/
theorem tooth_carmichael_561_passes_fermat_but_fails_pratt :
    lucasPowMod 384 2 560 561 = 1 ∧
    checkPrattStep [2, 3, 5, 7] ⟨561, 2, [(2, 4), (5, 1), (7, 1)]⟩ = false ∧ ¬ IsPrimeMod 561 := by
  refine ⟨by decide +kernel, by decide +kernel, fun hPrime => ?_⟩
  rcases hPrime.2 3 ⟨187, by decide⟩ with h1 | h561 <;> omega

#tooth_pair Qsag.checkPrattStep_sound vs Qsag.tooth_carmichael_561_passes_fermat_but_fails_pratt

/-- Complete 139-node Lucas–Pratt certificate DAG covering `p_pallas`, `q_pallas`, `r_bls381`, and `p_bls381`. -/
def prattCerts : List PrattCert :=
  [ ⟨19, 2, [(2, 1), (3, 2)]⟩, ⟨7, 3, [(2, 1), (3, 1)]⟩, ⟨13, 2, [(2, 2), (3, 1)]⟩, ⟨5, 2, [(2, 2)]⟩, ⟨53, 2, [(2, 2), (13, 1)]⟩,
    ⟨79, 3, [(2, 1), (3, 1), (13, 1)]⟩, ⟨43, 3, [(2, 1), (3, 1), (7, 1)]⟩, ⟨19267, 3, [(2, 1), (3, 1), (13, 2), (19, 1)]⟩, ⟨17, 3, [(2, 4)]⟩,
    ⟨71, 7, [(2, 1), (5, 1), (7, 1)]⟩, ⟨173, 2, [(2, 2), (43, 1)]⟩, ⟨2557, 2, [(2, 2), (3, 2), (71, 1)]⟩, ⟨757, 2, [(2, 2), (3, 3), (7, 1)]⟩,
    ⟨73, 5, [(2, 3), (3, 2)]⟩, ⟨29, 2, [(2, 2), (7, 1)]⟩, ⟨97, 5, [(2, 5), (3, 1)]⟩, ⟨449, 3, [(2, 6), (7, 1)]⟩, ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
    ⟨127, 3, [(2, 1), (3, 2), (7, 1)]⟩, ⟨41, 6, [(2, 3), (5, 1)]⟩, ⟨68477, 2, [(2, 2), (17, 1), (19, 1), (53, 1)]⟩,
    ⟨6091, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (29, 1)]⟩, ⟨191, 19, [(2, 1), (5, 1), (19, 1)]⟩, ⟨233, 3, [(2, 3), (29, 1)]⟩,
    ⟨281, 3, [(2, 3), (5, 1), (7, 1)]⟩, ⟨113, 3, [(2, 4), (7, 1)]⟩, ⟨137, 3, [(2, 3), (17, 1)]⟩, ⟨409, 21, [(2, 3), (3, 1), (17, 1)]⟩,
    ⟨151, 6, [(2, 1), (3, 1), (5, 2)]⟩, ⟨8101, 6, [(2, 2), (3, 4), (5, 2)]⟩, ⟨6229, 2, [(2, 2), (3, 2), (173, 1)]⟩,
    ⟨1327, 3, [(2, 1), (3, 1), (13, 1), (17, 1)]⟩, ⟨241, 7, [(2, 4), (3, 1), (5, 1)]⟩, ⟨181, 2, [(2, 2), (3, 2), (5, 1)]⟩, ⟨11, 2, [(2, 1), (5, 1)]⟩,
    ⟨10177, 7, [(2, 6), (3, 1), (53, 1)]⟩, ⟨2508409, 11, [(2, 3), (3, 4), (7, 2), (79, 1)]⟩, ⟨23, 5, [(2, 1), (11, 1)]⟩, ⟨47, 5, [(2, 1), (23, 1)]⟩,
    ⟨89, 3, [(2, 3), (11, 1)]⟩, ⟨2531, 2, [(2, 1), (5, 1), (11, 1), (23, 1)]⟩, ⟨115603, 2, [(2, 1), (3, 1), (19267, 1)]⟩,
    ⟨61, 2, [(2, 2), (3, 1), (5, 1)]⟩, ⟨1381, 2, [(2, 2), (3, 1), (5, 1), (23, 1)]⟩, ⟨294793, 10, [(2, 3), (3, 1), (71, 1), (173, 1)]⟩,
    ⟨47737, 5, [(2, 3), (3, 3), (13, 1), (17, 1)]⟩, ⟨1607, 5, [(2, 1), (11, 1), (73, 1)]⟩, ⟨18329, 3, [(2, 3), (29, 1), (79, 1)]⟩,
    ⟨609743, 5, [(2, 1), (7, 1), (97, 1), (449, 1)]⟩, ⟨829, 2, [(2, 2), (3, 2), (23, 1)]⟩, ⟨59, 2, [(2, 1), (29, 1)]⟩,
    ⟨1973, 2, [(2, 2), (17, 1), (29, 1)]⟩, ⟨509, 2, [(2, 2), (127, 1)]⟩, ⟨413527, 3, [(2, 1), (3, 1), (41, 3)]⟩,
    ⟨958679, 7, [(2, 1), (7, 1), (68477, 1)]⟩, ⟨827, 2, [(2, 1), (7, 1), (59, 1)]⟩, ⟨5701177, 7, [(2, 3), (3, 2), (13, 1), (6091, 1)]⟩,
    ⟨31649, 3, [(2, 5), (23, 1), (43, 1)]⟩, ⟨523, 2, [(2, 1), (3, 2), (29, 1)]⟩, ⟨941, 2, [(2, 2), (5, 1), (47, 1)]⟩,
    ⟨1686913, 10, [(2, 7), (3, 1), (23, 1), (191, 1)]⟩, ⟨467, 2, [(2, 1), (233, 1)]⟩, ⟨3373, 5, [(2, 2), (3, 1), (281, 1)]⟩,
    ⟨25741, 6, [(2, 2), (3, 2), (5, 1), (11, 1), (13, 1)]⟩, ⟨179, 2, [(2, 1), (89, 1)]⟩, ⟨3037, 2, [(2, 2), (3, 1), (11, 1), (23, 1)]⟩,
    ⟨2741, 2, [(2, 2), (5, 1), (137, 1)]⟩, ⟨51376543, 3, [(2, 1), (3, 1), (7, 1), (151, 1), (8101, 1)]⟩, ⟨24917, 2, [(2, 2), (6229, 1)]⟩,
    ⟨67, 2, [(2, 1), (3, 1), (11, 1)]⟩, ⟨977, 3, [(2, 4), (61, 1)]⟩, ⟨1151, 17, [(2, 1), (5, 2), (23, 1)]⟩,
    ⟨421987, 2, [(2, 1), (3, 1), (53, 1), (1327, 1)]⟩, ⟨125803, 3, [(2, 1), (3, 2), (29, 1), (241, 1)]⟩, ⟨947, 2, [(2, 1), (11, 1), (43, 1)]⟩,
    ⟨1453, 2, [(2, 2), (3, 1), (11, 2)]⟩, ⟨1087, 3, [(2, 1), (3, 1), (181, 1)]⟩, ⟨463, 3, [(2, 1), (3, 1), (7, 1), (11, 1)]⟩,
    ⟨1709, 3, [(2, 2), (7, 1), (61, 1)]⟩, ⟨24859, 2, [(2, 1), (3, 2), (1381, 1)]⟩, ⟨859267, 2, [(2, 1), (3, 2), (47737, 1)]⟩,
    ⟨906349, 2, [(2, 2), (3, 1), (47, 1), (1607, 1)]⟩, ⟨2529403, 2, [(2, 1), (3, 1), (23, 1), (18329, 1)]⟩,
    ⟨52437899, 2, [(2, 1), (43, 1), (609743, 1)]⟩, ⟨14923, 2, [(2, 1), (3, 2), (829, 1)]⟩, ⟨4229279, 13, [(2, 1), (827, 1), (2557, 1)]⟩,
    ⟨399082391, 7, [(2, 1), (5, 1), (7, 1), (5701177, 1)]⟩, ⟨20921, 3, [(2, 3), (5, 1), (523, 1)]⟩,
    ⟨475709467, 2, [(2, 1), (3, 1), (47, 1), (1686913, 1)]⟩, ⟨772231, 6, [(2, 1), (3, 1), (5, 1), (25741, 1)]⟩, ⟨359, 7, [(2, 1), (179, 1)]⟩,
    ⟨12149, 2, [(2, 2), (3037, 1)]⟩, ⟨16447, 3, [(2, 1), (3, 1), (2741, 1)]⟩, ⟨43670061551, 7, [(2, 1), (5, 2), (17, 1), (51376543, 1)]⟩,
    ⟨149503, 3, [(2, 1), (3, 1), (24917, 1)]⟩, ⟨269, 2, [(2, 2), (67, 1)]⟩, ⟨6942563, 2, [(2, 1), (11, 1), (17, 1), (19, 1), (977, 1)]⟩,
    ⟨110573, 3, [(2, 2), (7, 1), (11, 1), (359, 1)]⟩, ⟨755057, 3, [(2, 4), (41, 1), (1151, 1)]⟩,
    ⟨13090036741, 10, [(2, 2), (3, 1), (5, 1), (11, 1), (47, 1), (421987, 1)]⟩, ⟨2012849, 3, [(2, 4), (125803, 1)]⟩, ⟨7577, 3, [(2, 3), (947, 1)]⟩,
    ⟨43591, 11, [(2, 1), (3, 1), (5, 1), (1453, 1)]⟩, ⟨4349, 2, [(2, 2), (1087, 1)]⟩, ⟨125527, 5, [(2, 1), (3, 1), (20921, 1)]⟩,
    ⟨325086459374267, 2, [(2, 1), (509, 1), (413527, 1), (772231, 1)]⟩, ⟨4129989133, 5, [(2, 2), (3, 1), (359, 1), (958679, 1)]⟩,
    ⟨5239247429827, 2, [(2, 1), (3, 2), (757, 1), (12149, 1), (31649, 1)]⟩, ⟨897019, 2, [(2, 1), (3, 1), (149503, 1)]⟩,
    ⟨3767, 5, [(2, 1), (7, 1), (269, 1)]⟩, ⟨41655379, 2, [(2, 1), (3, 1), (6942563, 1)]⟩, ⟨2653753, 5, [(2, 3), (3, 1), (110573, 1)]⟩,
    ⟨3819663927398918131021, 6, [(2, 2), (3, 2), (5, 1), (19, 1), (113, 1), (755057, 1), (13090036741, 1)]⟩, ⟨4025699, 2, [(2, 1), (2012849, 1)]⟩,
    ⟨927093389, 3, [(2, 2), (13, 1), (409, 1), (43591, 1)]⟩, ⟨582767, 5, [(2, 1), (67, 1), (4349, 1)]⟩,
    ⟨10427374428728808478656897599072717, 2, [(2, 2), (294793, 1), (4229279, 1), (399082391, 1), (5239247429827, 1)]⟩,
    ⟨417677162933, 2, [(2, 2), (59, 1), (1973, 1), (897019, 1)]⟩, ⟨1197907, 3, [(2, 1), (3, 1), (53, 1), (3767, 1)]⟩,
    ⟨22160661629, 3, [(2, 2), (7, 1), (19, 1), (41655379, 1)]⟩, ⟨63690073, 7, [(2, 3), (3, 1), (2653753, 1)]⟩,
    ⟨1125266252156850182658904441386709967, 5, [(2, 1), (3373, 1), (43670061551, 1), (3819663927398918131021, 1)]⟩,
    ⟨80513981, 2, [(2, 2), (5, 1), (4025699, 1)]⟩, ⟨64881703735777, 5, [(2, 5), (3, 7), (927093389, 1)]⟩,
    ⟨9272813673901, 2, [(2, 2), (3, 1), (5, 2), (7, 1), (7577, 1), (582767, 1)]⟩,
    ⟨539204044132271846773, 5, [(2, 2), (3, 5), (89, 1), (14923, 1), (417677162933, 1)]⟩,
    ⟨8999194758858563409123804352480028797519453, 2, [(2, 2), (3, 4), (11, 1), (2531, 1), (115603, 1), (1197907, 1), (22160661629, 1), (325086459374267, 1)]⟩,
    ⟨254760293, 2, [(2, 2), (63690073, 1)]⟩, ⟨5247740253619, 2, [(2, 1), (3, 3), (17, 1), (71, 1), (80513981, 1)]⟩,
    ⟨92691255082156974996979, 3, [(2, 1), (3, 1), (31, 1), (467, 1), (16447, 1), (64881703735777, 1)]⟩,
    ⟨1928745244171409, 3, [(2, 4), (13, 1), (9272813673901, 1)]⟩,
    ⟨28948022309329048855892746252171976963363056481941560715954676764349967630337, 5, [(2, 32), (3, 1), (463, 1), (539204044132271846773, 1), (8999194758858563409123804352480028797519453, 1)]⟩,
    ⟨52435875175126190479447740508185965837690552500527637822603658699938581184513, 7, [(2, 32), (3, 1), (11, 1), (19, 1), (10177, 1), (125527, 1), (859267, 1), (906349, 2), (2508409, 1), (2529403, 1), (52437899, 1), (254760293, 2)]⟩,
    ⟨1690502597179744445941507, 2, [(2, 1), (3, 1), (13, 1), (4129989133, 1), (5247740253619, 1)]⟩,
    ⟨15778400344354997994418419698270088123916926905054652752758194827714659, 2, [(2, 1), (3, 1), (53, 1), (475709467, 1), (92691255082156974996979, 1), (1125266252156850182658904441386709967, 1)]⟩,
    ⟨7259797099061183477, 2, [(2, 2), (941, 1), (1928745244171409, 1)]⟩,
    ⟨28948022309329048855892746252171976963363056481941647379679742748393362948097, 5, [(2, 32), (3, 2), (1709, 1), (24859, 1), (1690502597179744445941507, 1), (10427374428728808478656897599072717, 1)]⟩,
    ⟨2584487767265781317813, 2, [(2, 2), (89, 1), (7259797099061183477, 1)]⟩,
    ⟨4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787, 2, [(2, 1), (3, 2), (11, 1), (23, 1), (47, 1), (10177, 1), (859267, 1), (52437899, 1), (2584487767265781317813, 1), (15778400344354997994418419698270088123916926905054652752758194827714659, 1)]⟩ ]

private theorem isPrimeMod_two : IsPrimeMod 2 :=
  ⟨by decide, fun d hd => by have := Nat.pos_of_dvd_of_pos hd (by decide); have := Nat.le_of_dvd (by decide) hd; omega⟩

private theorem isPrimeMod_three : IsPrimeMod 3 :=
  ⟨by decide, fun d hd => by
    have := Nat.pos_of_dvd_of_pos hd (by decide); have := Nat.le_of_dvd (by decide) hd
    if hd2 : d = 2 then subst hd2; obtain ⟨k, hk⟩ := hd; omega else omega⟩

private theorem prattCerts_valid : checkPrattDAG [2, 3] prattCerts = true := by decide +kernel
private def certifiedPrimeValues : List Nat := prattCerts.map PrattCert.n

private theorem mem_certifiedPrimeValues_prime {p : Nat} (hMem : p ∈ certifiedPrimeValues) : IsPrimeMod p := by
  obtain ⟨c, hcMem, rfl⟩ := List.mem_map.1 hMem
  refine checkPrattDAG_sound prattCerts [2, 3] (fun q hq => ?_) prattCerts_valid c hcMem
  cases hq with
  | head => exact isPrimeMod_two
  | tail _ hTail => cases hTail with | head => exact isPrimeMod_three | tail _ hNil => nomatch hNil

theorem p_pallas_isPrime : IsPrimeMod p_pallas := mem_certifiedPrimeValues_prime (by decide)
theorem q_pallas_isPrime : IsPrimeMod q_pallas := mem_certifiedPrimeValues_prime (by decide)
theorem r_bls381_isPrime : IsPrimeMod r_bls381 := mem_certifiedPrimeValues_prime (by decide)
theorem p_bls381_isPrime : IsPrimeMod p_bls381 := mem_certifiedPrimeValues_prime (by decide)

theorem pallas_and_bls381_moduli_prime :
    IsPrimeMod p_pallas ∧ IsPrimeMod q_pallas ∧ IsPrimeMod p_bls381 ∧ IsPrimeMod r_bls381 :=
  ⟨p_pallas_isPrime, q_pallas_isPrime, p_bls381_isPrime, r_bls381_isPrime⟩

/-! ## 3. Complete Projective RCB Addition, Curve Membership & Prime Subgroup Order (`[q]G = O`, `[r]G_1 = O`) -/

structure RcbProjPoint where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Repr

private def strictNatP (n : Nat) (k : Nat → RcbProjPoint) : RcbProjPoint :=
  match n with | 0 => k 0 | m + 1 => k (m + 1)
private def mkStrictPoint (x y z : Nat) : RcbProjPoint :=
  strictNatP x fun vx => strictNatP y fun vy => strictNatP z fun vz => ⟨vx, vy, vz⟩

def toRcbProj : SwPoint → RcbProjPoint | none => ⟨0, 1, 0⟩ | some (x, y) => ⟨x, y, 1⟩
def isProjIdentity (p : Nat) (P : RcbProjPoint) : Bool := (P.x % p == 0) && (P.y % p != 0) && (P.z % p == 0)
def projEqAffine (p : Nat) (P : RcbProjPoint) : SwPoint → Bool
  | none => isProjIdentity p P
  | some (ax, ay) => (P.z % p != 0) && ((P.x % p) == (ax * P.z) % p) && ((P.y % p) == (ay * P.z) % p)

/-- Eagerly reduced Renes–Costello–Batina (2016) Algorithm 7 complete addition for `a = 0`, `b3 = 3 * b`. -/
def rcbAdd (p b3 : Nat) (P Q : RcbProjPoint) : RcbProjPoint :=
  let addM := fun u v => (u + v) % p; let subM := fun u v => (u + p - (v % p)) % p; let mulM := fun u v => (u * v) % p
  strictNatP (mulM P.x Q.x) fun t0 => strictNatP (mulM P.y Q.y) fun t1 => strictNatP (mulM P.z Q.z) fun zz =>
  strictNatP (subM (mulM (addM P.x P.y) (addM Q.x Q.y)) (addM t0 t1)) fun t3 =>
  strictNatP (subM (mulM (addM P.y P.z) (addM Q.y Q.z)) (addM t1 zz)) fun t4 =>
  strictNatP (subM (mulM (addM P.x P.z) (addM Q.x Q.z)) (addM t0 zz)) fun y30 =>
  strictNatP ((3 * t0) % p) fun t03 => strictNatP (mulM b3 zz) fun t2 =>
  strictNatP (addM t1 t2) fun z30 => strictNatP (subM t1 t2) fun t1s => strictNatP (mulM b3 y30) fun cross =>
  mkStrictPoint (subM (mulM t3 t1s) (mulM t4 cross)) (addM (mulM t1s z30) (mulM cross t03))
    (addM (mulM z30 t4) (mulM t03 t3))

def rcbSmulFuel (p b3 : Nat) (base : RcbProjPoint) : Nat → Nat → RcbProjPoint
  | 0, _ => ⟨0, 1, 0⟩
  | fuel + 1, k =>
    if k = 0 then ⟨0, 1, 0⟩
    else let half := rcbSmulFuel p b3 base fuel (k / 2); let dbl := rcbAdd p b3 half half
         if k % 2 = 1 then rcbAdd p b3 dbl base else dbl

def rcbSmul (p b3 : Nat) (base : RcbProjPoint) (k : Nat) : RcbProjPoint := rcbSmulFuel p b3 base 256 k

theorem orchardSpendAuthG_onCurve_and_prime_subgroup_order :
    pallasCurve.onCurve orchardSpendAuthG = true ∧ pallasCurve.onCurve pastaPallasG = true ∧
    isProjIdentity p_pallas (rcbSmul p_pallas 15 (toRcbProj orchardSpendAuthG) q_pallas) = true ∧
    isProjIdentity p_pallas (rcbSmul p_pallas 15 (toRcbProj pastaPallasG) q_pallas) = true ∧
    projEqAffine p_pallas (rcbSmul p_pallas 15 (toRcbProj orchardSpendAuthG) (q_pallas - 1))
      (pallasCurve.neg orchardSpendAuthG) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem bls381G1_onCurve_and_prime_subgroup_order :
    bls381Curve.onCurve bls381G1 = true ∧
    isProjIdentity p_bls381 (rcbSmul p_bls381 12 (toRcbProj bls381G1) r_bls381) = true ∧
    projEqAffine p_bls381 (rcbSmul p_bls381 12 (toRcbProj bls381G1) (r_bls381 - 1))
      (bls381Curve.neg bls381G1) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

def bls381Torsion3Point : SwPoint := some (0, 2)

/-- `#tooth` `BLS12-381` 3-torsion point `(0, 2)` lies on `y^2 = x^3 + 4` yet fails `[r_bls381]P = O`. -/
theorem tooth_bls381_torsion3_onCurve_but_off_subgroup :
    bls381Curve.onCurve bls381Torsion3Point = true ∧
    isProjIdentity p_bls381 (rcbSmul p_bls381 12 (toRcbProj bls381Torsion3Point) 3) = true ∧
    isProjIdentity p_bls381 (rcbSmul p_bls381 12 (toRcbProj bls381Torsion3Point) r_bls381) = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

#tooth_pair Qsag.bls381G1_onCurve_and_prime_subgroup_order vs Qsag.tooth_bls381_torsion3_onCurve_but_off_subgroup

theorem projEqAffine_zk_constraint_sound {p ax ay : Nat} {P : RcbProjPoint} {zInv : Nat}
    (hAx : ax < p) (hAy : ay < p) (hZInv : (P.z * zInv) % p = 1)
    (hX : P.x % p = (ax * P.z) % p) (hY : P.y % p = (ay * P.z) % p) :
    P.z % p ≠ 0 ∧ (P.x * zInv) % p = ax ∧ (P.y * zInv) % p = ay := by
  have hZNe : P.z % p ≠ 0 := fun hz0 => by
    have : (P.z * zInv) % p = 0 := by rw [Nat.mul_mod, hz0, Nat.zero_mul, Nat.zero_mod]
    omega
  have hCoord : ∀ {coord aff : Nat}, aff < p → coord % p = (aff * P.z) % p → (coord * zInv) % p = aff := by
    intro coord aff hLt hEq
    calc (coord * zInv) % p = (((aff * P.z) % p) * (zInv % p)) % p := by rw [Nat.mul_mod, hEq]
      _ = (aff * (P.z * zInv)) % p := by rw [← Nat.mul_mod, Nat.mul_assoc]
      _ = ((aff % p) * 1) % p := by rw [Nat.mul_mod, hZInv]
      _ = aff := by rw [Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hLt]
  exact ⟨hZNe, hCoord hAx hX, hCoord hAy hY⟩

/-! ## 4. 3-Party ZKBoo 2-of-3 Knowledge Extraction & RedPallas Rerandomized `rk` Unlinkability -/

structure PrimeSubgroup (C : SwCurve) (G : SwPoint) (ord : Nat) where
  add : SwPoint → SwPoint → SwPoint
  smul : Nat → SwPoint
  p_prime : IsPrimeMod C.p
  ord_prime : IsPrimeMod ord
  gen_onCurve : C.onCurve G = true
  add_none_left : ∀ P, add none P = P
  smul_add : ∀ a b, smul (a + b) = add (smul a) (smul b)
  smul_ord : smul ord = none
  exact_ord : ∀ k, 0 < k → k < ord → smul k ≠ none

theorem PrimeSubgroup.smul_injective {C : SwCurve} {G : SwPoint} {ord : Nat}
    (grp : PrimeSubgroup C G ord) {a b : Nat} (ha : a < ord) (hb : b < ord) (hEq : grp.smul a = grp.smul b) :
    a = b := by
  have hNeLt : ∀ {u v : Nat}, u < v → v < ord → grp.smul u ≠ grp.smul v := fun {u v} huv hv heq => by
    have h1 : grp.smul ((ord - u) + v) = none := by
      rw [grp.smul_add, ← heq, ← grp.smul_add, show (ord - u) + u = ord by omega, grp.smul_ord]
    have h2 : grp.smul ((ord - u) + v) = grp.smul (v - u) := by
      rw [show (ord - u) + v = ord + (v - u) by omega, grp.smul_add, grp.smul_ord, grp.add_none_left]
    exact grp.exact_ord (v - u) (by omega) (by omega) (h2.symm.trans h1)
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · exact False.elim (hNeLt hlt hb hEq)
  · exact heq
  · exact False.elim (hNeLt hgt ha hEq.symm)

def zkbooReconstructScalar (ord s0 s1 s2 : Nat) : Nat := (s0 + s1 + s2) % ord
def zkbooOpenedPair (shares : Fin 3 → Nat) (e : Fin 3) : Nat × Nat :=
  (shares e, shares ⟨(e.val + 1) % 3, Nat.mod_lt _ (by decide)⟩)

def extractThreeShares (e1 e2 : Fin 3) (p1 p2 : Nat × Nat) : Nat × Nat × Nat :=
  if e1.val = 0 then (if e2.val = 1 then (p1.1, p1.2, p2.2) else (p1.1, p1.2, p2.1))
  else if e1.val = 1 then (if e2.val = 0 then (p2.1, p1.1, p1.2) else (p2.2, p1.1, p1.2))
  else (if e2.val = 0 then (p1.2, p2.2, p1.1) else (p1.2, p2.1, p1.1))

theorem extractThreeShares_complete (shares : Fin 3 → Nat) (e1 e2 : Fin 3) (hNe : e1 ≠ e2) :
    extractThreeShares e1 e2 (zkbooOpenedPair shares e1) (zkbooOpenedPair shares e2) =
      (shares 0, shares 1, shares 2) := by
  rcases e1 with ⟨v1, hv1⟩; rcases e2 with ⟨v2, hv2⟩
  have hNeVal : v1 ≠ v2 := fun h => hNe (Fin.ext h)
  unfold extractThreeShares zkbooOpenedPair
  match v1, hv1, v2, hv2 with
  | 0, _, 0, _ => exact False.elim (hNeVal rfl) | 0, _, 1, _ => rfl | 0, _, 2, _ => rfl
  | 1, _, 0, _ => rfl | 1, _, 1, _ => exact False.elim (hNeVal rfl) | 1, _, 2, _ => rfl
  | 2, _, 0, _ => rfl | 2, _, 1, _ => rfl | 2, _, 2, _ => exact False.elim (hNeVal rfl)
  | _ + 3, hv, _, _ => omega | 0, _, _ + 3, hv => omega | 1, _, _ + 3, hv => omega | 2, _, _ + 3, hv => omega

def ZkBooDlogCommitted {C : SwCurve} {G : SwPoint} {ord : Nat}
    (grp : PrimeSubgroup C G ord) (pk : SwPoint) (shares : Fin 3 → Nat) : Prop :=
  let sk := zkbooReconstructScalar ord (shares 0) (shares 1) (shares 2)
  0 < sk ∧ sk < ord ∧ grp.smul sk = pk

theorem zkboo_two_challenge_extraction_sound {C : SwCurve} {G pk : SwPoint} {ord : Nat}
    (grp : PrimeSubgroup C G ord) (shares : Fin 3 → Nat) (e1 e2 : Fin 3) (hNe : e1 ≠ e2)
    (hValid : ZkBooDlogCommitted grp pk shares) :
    let (s0, s1, s2) := extractThreeShares e1 e2 (zkbooOpenedPair shares e1) (zkbooOpenedPair shares e2)
    let sk := zkbooReconstructScalar ord s0 s1 s2
    0 < sk ∧ sk < ord ∧ grp.smul sk = pk ∧ (∀ sk' : Nat, sk' < ord → grp.smul sk' = pk → sk' = sk) := by
  rw [extractThreeShares_complete shares e1 e2 hNe]
  dsimp only [ZkBooDlogCommitted] at hValid ⊢; obtain ⟨hPos, hLt, hSmul⟩ := hValid
  exact ⟨hPos, hLt, hSmul, fun sk' hLt' hSmul' => grp.smul_injective hLt' hLt (hSmul'.trans hSmul.symm)⟩

/-- `#tooth` A single ZKBoo challenge `(s0, s1)` information-theoretically hides `sk`. -/
theorem tooth_zkboo_single_challenge_information_theoretically_hides_witness
    {ord s0 s1 skA skB : Nat} (hA : skA < ord) (hB : skB < ord) (hNe : skA ≠ skB) :
    ∃ s2A s2B : Nat, s2A < ord ∧ s2B < ord ∧ s2A ≠ s2B ∧
      zkbooReconstructScalar ord s0 s1 s2A = skA ∧ zkbooReconstructScalar ord s0 s1 s2B = skB := by
  have hOrdPos : 0 < ord := by omega
  let sum01 := (s0 + s1) % ord
  have hSumLt : sum01 < ord := Nat.mod_lt _ hOrdPos
  have hSolve : ∀ {sk : Nat}, sk < ord → zkbooReconstructScalar ord s0 s1 ((sk + ord - sum01) % ord) = sk :=
    fun {sk} hSk => by
      unfold zkbooReconstructScalar
      rw [Nat.add_mod_mod, ← Nat.mod_add_mod,
          show (s0 + s1) % ord + (sk + ord - sum01) = ord + sk by dsimp only [sum01]; omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt hSk]
  have hRecA := hSolve hA; have hRecB := hSolve hB
  refine ⟨(skA + ord - sum01) % ord, (skB + ord - sum01) % ord,
    Nat.mod_lt _ hOrdPos, Nat.mod_lt _ hOrdPos, fun hEq => ?_, hRecA, hRecB⟩
  rw [hEq, hRecB] at hRecA; exact hNe hRecA.symm

#tooth_pair Qsag.zkboo_two_challenge_extraction_sound vs
  Qsag.tooth_zkboo_single_challenge_information_theoretically_hides_witness

@[expose] def redpallasEffectiveScalar (ord ask alpha : Nat) : Nat := (ask + alpha) % ord
@[expose] def redpallasSolveAlpha (ord rsk ask : Nat) : Nat := (rsk + ord - (ask % ord)) % ord

theorem primeSubgroup_smul_add_mod {C : SwCurve} {G : SwPoint} {ord : Nat}
    (grp : PrimeSubgroup C G ord) {ask alpha : Nat} (hAsk : ask < ord) (hAlpha : alpha < ord) :
    grp.smul (redpallasEffectiveScalar ord ask alpha) = grp.add (grp.smul ask) (grp.smul alpha) := by
  unfold redpallasEffectiveScalar; rw [← grp.smul_add]
  if hLt : ask + alpha < ord then rw [Nat.mod_eq_of_lt hLt]
  else
    have hMod : (ask + alpha) % ord = ask + alpha - ord := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hMod, show ask + alpha = ord + (ask + alpha - ord) by omega, grp.smul_add, grp.smul_ord, grp.add_none_left]

theorem orchard_redpallas_rerandomized_extraction_sound {C : SwCurve} {G rk : SwPoint}
    (grp : PrimeSubgroup C G q_pallas) (askShares alphaShares : Fin 3 → Nat) (e1 e2 : Fin 3) (hNe : e1 ≠ e2)
    (hAskRange : 0 < zkbooReconstructScalar q_pallas (askShares 0) (askShares 1) (askShares 2) ∧
                 zkbooReconstructScalar q_pallas (askShares 0) (askShares 1) (askShares 2) < q_pallas)
    (hAlphaRange : zkbooReconstructScalar q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2) < q_pallas)
    (hRskPos : 0 < redpallasEffectiveScalar q_pallas
      (zkbooReconstructScalar q_pallas (askShares 0) (askShares 1) (askShares 2))
      (zkbooReconstructScalar q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2)))
    (hCurve : grp.smul (redpallasEffectiveScalar q_pallas
      (zkbooReconstructScalar q_pallas (askShares 0) (askShares 1) (askShares 2))
      (zkbooReconstructScalar q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2))) = rk) :
    let (a0, a1, a2) := extractThreeShares e1 e2 (zkbooOpenedPair askShares e1) (zkbooOpenedPair askShares e2)
    let (r0, r1, r2) := extractThreeShares e1 e2 (zkbooOpenedPair alphaShares e1) (zkbooOpenedPair alphaShares e2)
    let ask := zkbooReconstructScalar q_pallas a0 a1 a2
    let alpha := zkbooReconstructScalar q_pallas r0 r1 r2
    let rsk := redpallasEffectiveScalar q_pallas ask alpha
    0 < ask ∧ ask < q_pallas ∧ alpha < q_pallas ∧ 0 < rsk ∧ rsk < q_pallas ∧
    grp.add (grp.smul ask) (grp.smul alpha) = rk ∧
    (∀ ask' alpha' : Nat, ask' < q_pallas → alpha' < q_pallas →
      grp.add (grp.smul ask') (grp.smul alpha') = rk → redpallasEffectiveScalar q_pallas ask' alpha' = rsk) := by
  rw [extractThreeShares_complete askShares e1 e2 hNe, extractThreeShares_complete alphaShares e1 e2 hNe]
  dsimp only; have hQPos : 0 < q_pallas := by decide
  have hRskLt := Nat.mod_lt (zkbooReconstructScalar q_pallas (askShares 0) (askShares 1) (askShares 2) +
    zkbooReconstructScalar q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2)) hQPos
  have hHom := primeSubgroup_smul_add_mod grp hAskRange.2 hAlphaRange
  refine ⟨hAskRange.1, hAskRange.2, hAlphaRange, hRskPos, hRskLt, hHom.symm.trans hCurve, ?_⟩
  intro ask' alpha' hAsk' hAlpha' hRk'
  exact grp.smul_injective (Nat.mod_lt _ hQPos) hRskLt
    (((primeSubgroup_smul_add_mod grp hAsk' hAlpha').trans hRk').trans hCurve.symm)

theorem orchard_redpallas_rk_perfect_unlinkability {ord rsk ask : Nat} (hRsk : rsk < ord) (hAsk : ask < ord) :
    let alpha := redpallasSolveAlpha ord rsk ask
    alpha < ord ∧ redpallasEffectiveScalar ord ask alpha = rsk ∧
    (∀ alpha' : Nat, alpha' < ord → redpallasEffectiveScalar ord ask alpha' = rsk → alpha' = alpha) := by
  have hOrdPos : 0 < ord := by omega
  dsimp only; have hAskMod : ask % ord = ask := Nat.mod_eq_of_lt hAsk
  have hHit : redpallasEffectiveScalar ord ask (redpallasSolveAlpha ord rsk ask) = rsk := by
    unfold redpallasEffectiveScalar redpallasSolveAlpha
    rw [hAskMod, Nat.add_mod_mod, show ask + (rsk + ord - ask) = ord + rsk by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hRsk]
  refine ⟨Nat.mod_lt _ hOrdPos, hHit, fun alpha' hAlpha' hEq' => ?_⟩
  unfold redpallasEffectiveScalar at hEq'; unfold redpallasSolveAlpha; rw [hAskMod, ← hEq']
  if hSumLt : ask + alpha' < ord then
    rw [Nat.mod_eq_of_lt hSumLt, show ask + alpha' + ord - ask = ord + alpha' by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hAlpha']
  else
    have hModSub : (ask + alpha') % ord = ask + alpha' - ord := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hModSub, show ask + alpha' - ord + ord - ask = alpha' by omega, Nat.mod_eq_of_lt hAlpha']

/-- `#tooth` Setting `alpha = 0` collapses RedPallas unlinkability (`redpallasEffectiveScalar q_pallas ask 0 = ask`). -/
theorem tooth_redpallas_zero_alpha_links_ak :
    ∃ ask1 ask2 : Nat, 0 < ask1 ∧ ask1 < q_pallas ∧ 0 < ask2 ∧ ask2 < q_pallas ∧ ask1 ≠ ask2 ∧
      redpallasEffectiveScalar q_pallas ask1 0 ≠ redpallasEffectiveScalar q_pallas ask2 0 ∧
      redpallasSolveAlpha q_pallas ask1 ask2 ≠ 0 :=
  ⟨1, 2, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

#tooth_pair Qsag.orchard_redpallas_rk_perfect_unlinkability vs Qsag.tooth_redpallas_zero_alpha_links_ak

/-! ## 5. Constructive Axiom Audit (`#verify_constructive`) -/

#verify_constructive
  Qsag.pallas_and_bls381_limbs_and_bit_bounds Qsag.IsPrimeMod.dvd_mul Qsag.lucasPowMod_eq_pow_mod
  Qsag.isPrime_of_lucas_pratt Qsag.checkPrattStep_sound Qsag.checkPrattDAG_sound
  Qsag.tooth_carmichael_561_passes_fermat_but_fails_pratt
  Qsag.p_pallas_isPrime Qsag.q_pallas_isPrime Qsag.r_bls381_isPrime Qsag.p_bls381_isPrime
  Qsag.pallas_and_bls381_moduli_prime Qsag.orchardSpendAuthG_onCurve_and_prime_subgroup_order
  Qsag.bls381G1_onCurve_and_prime_subgroup_order Qsag.tooth_bls381_torsion3_onCurve_but_off_subgroup
  Qsag.projEqAffine_zk_constraint_sound Qsag.PrimeSubgroup.smul_injective Qsag.extractThreeShares_complete
  Qsag.zkboo_two_challenge_extraction_sound
  Qsag.tooth_zkboo_single_challenge_information_theoretically_hides_witness
  Qsag.primeSubgroup_smul_add_mod Qsag.orchard_redpallas_rerandomized_extraction_sound
  Qsag.orchard_redpallas_rk_perfect_unlinkability Qsag.tooth_redpallas_zero_alpha_links_ak

end Qsag
